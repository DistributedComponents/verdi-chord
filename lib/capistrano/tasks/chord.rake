require 'digest'

namespace :chord do

  def chord_log_path
    "#{shared_path}/extraction/chord/log/chord.log"
  end

  def client_log_path
    "#{shared_path}/extraction/chord/log/client.log"
  end

  def chord_pidfile_path
    "#{shared_path}/extraction/chord/tmp/chord.pid"
  end

  desc 'start chord ring'
  task :start do
    ring = roles(:node).collect { |node| "-ring #{node.properties.ip}:#{fetch(:chord_node_port)}" }.join(' ')
    on roles(:node) do |node|
      execute '/sbin/start-stop-daemon',
        '--start',
        '--quiet',
        '--oknodo',
        '--make-pidfile',
        "--pidfile #{chord_pidfile_path}",
        '--background',
        "--chdir #{current_path}/extraction/chord",
        '--startas /bin/bash',
        "-- -c 'exec ./chord.native -bind #{node.properties.ip}:#{fetch(:chord_node_port)} #{ring} > log/chord.log 2>&1'"
    end
  end

  desc 'start chord ring base'
  task :start_base do
    ring = roles([:root, :base]).collect { |node| "-ring #{node.properties.ip}:#{fetch(:chord_node_port)}" }.join(' ')
    on roles(:base) do |node|
      execute '/sbin/start-stop-daemon',
        '--start',
        '--quiet',
        '--oknodo',
        '--make-pidfile',
        "--pidfile #{chord_pidfile_path}",
        '--background',
        "--chdir #{current_path}/extraction/chord",
        '--startas /bin/bash',
        "-- -c 'exec ./chord.native -bind #{node.properties.ip}:#{fetch(:chord_node_port)} #{ring} > log/chord.log 2>&1'"
    end
  end

  desc 'start chord with known'
  task :start_known do
    nodes = Hash[roles(:node).collect { |node| [node.properties.name, node] }]
    on roles(:node) do |node|
      known = nodes[ENV['KNOWN']]
      execute '/sbin/start-stop-daemon',
        '--start',
        '--quiet',
        '--oknodo',
        '--make-pidfile',
        "--pidfile #{chord_pidfile_path}",
        '--background',
        "--chdir #{current_path}/extraction/chord",
        '--startas /bin/bash',
        "-- -c 'exec ./chord.native -bind #{node.properties.ip}:#{fetch(:chord_node_port)} -known #{known.properties.ip}:#{fetch(:chord_node_port)} > log/chord.log 2>&1'"
    end
  end

  desc 'start chord ext'
  task :start_ext do
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
        "--chdir #{current_path}/extraction/chord",
        '--startas /bin/bash',
        "-- -c 'exec ./chord.native -bind #{node.properties.ip}:#{fetch(:chord_node_port)} -known #{known.properties.ip}:#{fetch(:chord_node_port)} > log/chord.log 2>&1'"
    end
  end

  desc 'stop chord'
  task :stop do
    on roles(:node) do
      execute '/sbin/start-stop-daemon',
        '--stop',
        '--oknodo',
        "--pidfile #{chord_pidfile_path}"
    end
  end

  desc 'tail chord log'
  task :tail_log do
    on roles(:node) do
      execute 'tail', '-n 20', chord_log_path
    end
  end

  desc 'truncate chord log'
  task :truncate_log do
    on roles(:node) do
      execute 'truncate', '-s 0', chord_log_path
    end
  end

  desc 'truncate client log'
  task :truncate_client_log do
    on roles(:client) do
      execute 'truncate', '-s 0', client_log_path
    end
  end

  desc 'print entire chord log'
  task :get_log do
    on roles(:node) do
      execute 'cat', chord_log_path
    end
  end

  desc 'print entire client log'
  task :get_client_log do
    on roles(:client) do
      execute 'cat', client_log_path
    end
  end

  desc 'client get ptrs'
  task :client_get_ptrs do
    nodes = Hash[roles(:node).collect { |node| [node.properties.name, node] }]
    node = nodes[ENV['NODE']]
    on roles(:client) do |client|
      execute "#{current_path}/extraction/chord/client.native",
        "-bind #{client.properties.ip}",
        "-node #{node.properties.ip}:#{fetch(:chord_node_port)}",
        "-query get_ptrs"
    end
  end

  desc 'client get ptrs locally'
  task :client_local_get_ptrs do
    nodes = Hash[roles(:node).collect { |node| [node.properties.name, node] }]
    node = nodes[ENV['NODE']]
    run_locally do
      execute 'extraction/chord/client.native',
        '-bind 0.0.0.0',
        "-node #{node.properties.ip}:#{fetch(:chord_node_port)}",
        '-query get_ptrs'
    end
  end

  # echo -n rdoenges | md5sum | awk '{print $1}'
  desc 'client lookup'
  task :client_lookup do
    nodes = Hash[roles(:node).collect { |node| [node.properties.name, node] }]
    node = nodes[ENV['NODE']]
    hash = Digest::MD5.hexdigest(ENV['QUERY'])
    on roles(:client) do |client|
      execute "echo \"query: #{ENV['QUERY']} (#{hash})\" >> #{client_log_path} 2>&1"
      execute "#{current_path}/extraction/chord/client.native",
        "-bind #{client.properties.ip}",
        "-node #{node.properties.ip}:#{fetch(:chord_node_port)}",
        "-query lookup #{hash} >> #{client_log_path} 2>&1"
    end
  end

  desc 'client lookup locally'
  task :client_local_lookup do
    nodes = Hash[roles(:node).collect { |node| [node.properties.name, node] }]
    node = nodes[ENV['NODE']]
    hash = Digest::MD5.hexdigest(ENV['QUERY'])
    run_locally do
      execute 'extraction/chord/client.native',
        '-bind 0.0.0.0',
        "-node #{node.properties.ip}:#{fetch(:chord_node_port)}",
        "-query lookup #{hash}"
    end
  end

  desc 'experiment 1'
  task :experiment_1 do
    names = roles(:node).collect { |node| node.properties.name }

    # 0. truncate logs
    Rake::Task['chord:truncate_log'].execute
    Rake::Task['chord:truncate_client_log'].execute

    # 1. start up whole ring
    Rake::Task['chord:start'].execute

    # 2. pause 20 seconds
    sleep(20)

    # 3. send queries
    f = File.open('words10.txt')
    words = f.readlines
    words.each do |word|
      ENV['NODE'] = names.sample
      ENV['QUERY'] = word.strip
      Rake::Task['chord:client_lookup'].execute
      sleep(5)
    end

    # 4. stop ring
    Rake::Task['chord:stop'].execute
  end

  desc 'experiment 2'
  task :experiment_2 do
    names = roles(:node).collect { |node| node.properties.name }
    nodes = Hash[roles(:node).collect { |node| [node.properties.name, node] }]

    # 0. truncate logs
    Rake::Task['chord:truncate_log'].execute
    Rake::Task['chord:truncate_client_log'].execute

    # 1. start up whole ring
    Rake::Task['chord:start'].execute

    # 2. pause 20 seconds
    sleep(20)
    
    # 3. send first set of queries
    f = File.open('words10.txt')
    words = f.readlines
    words.each do |word|
      ENV['NODE'] = names.sample
      ENV['QUERY'] = word.strip
      Rake::Task['chord:client_lookup'].execute
      sleep(5)
    end

    # 4. stop one randomly chosen node
    stopped = names.sample
    node = nodes[stopped]
    on node do
      execute '/sbin/start-stop-daemon',
        '--stop',
        '--oknodo',
        "--pidfile #{chord_pidfile_path}"
    end

    # 5. send second set of queries
    names = names - [stopped]
    words.each do |word|
      ENV['NODE'] = names.sample
      ENV['QUERY'] = word.strip
      Rake::Task['chord:client_lookup'].execute
      sleep(5)
    end

    # 4. stop ring
    Rake::Task['chord:stop'].execute
  end

  desc 'experiment 3'
  task :experiment_3 do
    # for lookup
    nodes = Hash[roles(:node).collect { |node| [node.properties.name, node] }]
    
    # 0. truncate logs
    Rake::Task['chord:truncate_log'].execute
    Rake::Task['chord:truncate_client_log'].execute

    # 1. start up 4 "randomly" chosen nodes
    ring = roles([:root, :base]).collect { |node| "-ring #{node.properties.ip}:#{fetch(:chord_node_port)}" }.join(' ')
    on roles([:root, :base]) do |node|
      execute '/sbin/start-stop-daemon',
        '--start',
        '--quiet',
        '--oknodo',
        '--make-pidfile',
        "--pidfile #{chord_pidfile_path}",
        '--background',
        "--chdir #{current_path}/extraction/chord",
        '--startas /bin/bash',
        "-- -c 'exec ./chord.native -bind #{node.properties.ip}:#{fetch(:chord_node_port)} #{ring} > log/chord.log 2>&1'"
    end

    # 2. pause to stabilize 4-node ring
    sleep(20)

    # 3. start 4 new "randomly" chosen nodes
    on roles(:ext) do |node|
      known = nodes[node.properties.known]
      execute '/sbin/start-stop-daemon',
        '--start',
        '--quiet',
        '--oknodo',
        '--make-pidfile',
        "--pidfile #{chord_pidfile_path}",
        '--background',
        "--chdir #{current_path}/extraction/chord",
        '--startas /bin/bash',
        "-- -c 'exec ./chord.native -bind #{node.properties.ip}:#{fetch(:chord_node_port)} -known #{known.properties.ip}:#{fetch(:chord_node_port)} > log/chord.log 2>&1'"
    end

    # 4. pause to stabilize 8-node ring
    sleep(20)

    # 5. shut down the 4 new nodes
    on roles(:ext) do
      execute '/sbin/start-stop-daemon',
        '--stop',
        '--oknodo',
        "--pidfile #{chord_pidfile_path}"
    end

    # 6. pause to stabilize 4-node ring
    sleep(20)

    # 7. stop remaining nodes
    on roles([:root, :base]) do
      execute '/sbin/start-stop-daemon',
        '--stop',
        '--oknodo',
        "--pidfile #{chord_pidfile_path}"
    end

  end

end
