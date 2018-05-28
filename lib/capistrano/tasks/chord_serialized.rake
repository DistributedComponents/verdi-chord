namespace :chord_serialized do

  def chord_serialized_log_path
    "#{shared_path}/extraction/chord-serialized/log/chord-serialized.log"
  end

  def chord_serialized_pidfile_path
    "#{shared_path}/extraction/chord-serialized/tmp/chord-serialized.pid"
  end

  desc 'start serialized chord ring'
  task :start do
    ring = roles(:node).collect { |node| "-ring #{node.properties.ip}:#{fetch(:chord_serialized_node_port)}" }.join(' ')
    on roles(:node) do |node|
      execute '/sbin/start-stop-daemon',
        '--start',
        '--quiet',
        '--oknodo',
        '--make-pidfile',
        "--pidfile #{chord_serialized_pidfile_path}",
        '--background',
        "--chdir #{current_path}/extraction/chord-serialized",
        '--startas /bin/bash',
        "-- -c 'exec ./chordserialized.native -bind #{node.properties.ip}:#{fetch(:chord_serialized_node_port)} #{ring} > log/chord-serialized.log 2>&1'"
    end
  end

  desc 'start serialized chord with known'
  task :start_known do
    nodes = Hash[roles(:node).collect { |node| [node.properties.name, node] }]
    on roles(:node) do |node|
      known = nodes[node.properties.known]
      execute '/sbin/start-stop-daemon',
        '--start',
        '--quiet',
        '--oknodo',
        '--make-pidfile',
        "--pidfile #{chord_pidfile_path}",
        '--background',
        "--chdir #{current_path}/extraction/chord-serialized",
        '--startas /bin/bash',
        "-- -c 'exec ./chordserialized.native -bind #{node.properties.ip}:#{fetch(:chord_serialized_node_port)} -known #{known.properties.ip}:#{fetch(:chord_serialized_node_port)} > log/chord-serialized.log 2>&1'"
    end
  end

  desc 'stop serialized chord'
  task :stop do
    on roles(:node) do
      execute '/sbin/start-stop-daemon',
        '--stop',
        '--oknodo',
        "--pidfile #{chord_serialized_pidfile_path}"
    end
  end

  desc 'tail serialized chord log'
  task :tail_log do
    on roles(:node) do
      execute 'tail', '-n 20', chord_serialized_log_path
    end
  end

  desc 'truncate serialized chord log'
  task :truncate_log do
    on roles(:node) do
      execute 'truncate', '-s 0', chord_serialized_log_path
    end
  end

  desc 'print entire serialized chord log'
  task :get_log do
    on roles(:node) do
      execute 'cat', chord_serialized_log_path
    end
  end

  desc 'client get ptrs'
  task :client_get_ptrs do
    nodes = Hash[roles(:node).collect { |node| [node.properties.name, node] }]
    node = nodes[ENV['NODE']]
    on roles(:client) do |client|
      execute "#{current_path}/extraction/chord-serialized/client.native",
        "-bind #{client.properties.ip}",
        "-node #{node.properties.ip}:#{fetch(:chord_serialized_node_port)}",
        "-query get_ptrs"
    end
  end

  desc 'client get ptrs locally'
  task :client_local_get_ptrs do
    nodes = Hash[roles(:node).collect { |node| [node.properties.name, node] }]
    node = nodes[ENV['NODE']]
    run_locally do
      execute 'extraction/chord-serialized/client.native',
              '-bind 0.0.0.0',
        "-node #{node.properties.ip}:#{fetch(:chord_serialized_node_port)}",
        '-query get_ptrs'
    end
  end

  desc 'client lookup'
  task :client_lookup do
    nodes = Hash[roles(:node).collect { |node| [node.properties.name, node] }]
    node = nodes[ENV['NODE']]
    on roles(:client) do |client|
      execute "#{current_path}/extraction/chord-serialized/client.native",
        "-bind #{client.properties.ip}",
        "-node #{node.properties.ip}:#{fetch(:chord_serialized_node_port)}",
        "-query lookup #{ENV['HASH']}"
    end
  end

  desc 'client lookup locally'
  task :client_local_lookup do
    nodes = Hash[roles(:node).collect { |node| [node.properties.name, node] }]
    node = nodes[ENV['NODE']]
    run_locally do
      execute 'extraction/chord-serialized/client.native',
        '-bind 0.0.0.0',
        "-node #{node.properties.ip}:#{fetch(:chord_serialized_node_port)}",
        "-query lookup #{ENV['HASH']}"
    end
  end

  # bad
  def join h
    ENV['HOSTS'] = h
    Rake::Task["chord_serialized:start_known"].execute
    ENV['HOSTS'] = nil
  end

  # bad
  def part h
    ENV['HOSTS'] = 'discoberry02.cs.washington.edu'
    Rake::Task["chord_serialized:stop"].execute
    ENV['HOSTS'] = nil
  end

  def lookup (n, k)
    ENV['NODE'] = n
    ENV['HASH'] = k
    Rake::Task["chord_serialized:client_lookup"].execute
    ENV['NODE'] = nil
    ENV['HASH'] = nil
  end

  desc 'experiment 1'
  task :experiment_1 do
    # 0. truncate logs
    Rake::Task["chord_serialized:truncate_log"].execute

    # 1. start up whole ring
    Rake::Task["chord_serialized:start"].execute

    # 2. pause 20 seconds
    sleep(20)

    # 3. send queries
    n = '211'
    k = '66e3ec3f16c5a8071d00b917ce3cc992'

    lookup n, k
    sleep(10)
    lookup n, k
    sleep(10)

    # 4. stop ring
    Rake::Task["chord_serialized:stop"].execute
  end
end
