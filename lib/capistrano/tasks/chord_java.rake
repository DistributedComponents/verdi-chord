namespace :chord_java do

  def chord_java_pidfile_path
    "#{shared_path}/extraction/chord/tmp/chord_java.pid"
  end

  def chord_java_log_path
    "#{shared_path}/extraction/chord/log/chord_java.log"
  end

  desc 'test start'
  task :test_start do
    on roles(:root) do |node|
      execute '/sbin/start-stop-daemon',
        '--start',
        '--quiet',
        '--oknodo',
        '--make-pidfile',
        "--pidfile #{chord_java_pidfile_path}",
        '--background',
        "--chdir #{current_path}/../../../ChordJava",
        '--startas /bin/bash',
        "-- -c 'exec java Chord #{node.properties.ip}:#{fetch(:chord_node_port)} > #{chord_java_log_path} 2>&1'"
    end
  end

  desc 'test stop'
  task :test_stop do
    on roles(:root) do
      execute '/sbin/start-stop-daemon',
        '--stop',
        '--oknodo',
        "--pidfile #{chord_java_pidfile_path}"
    end
  end

  desc 'experiment 3'
  task :experiment_3 do
    # for reference
    nodes = Hash[roles(:node).collect { |node| [node.properties.name, node] }]    
    root = roles(:root).first

    # 0. truncate logs
    Rake::Task['chord_java:truncate_log'].execute

    # 1. start up 4 "randomly" chosen nodes
    on roles(:root) do |node|
      execute '/sbin/start-stop-daemon',
        '--start',
        '--quiet',
        '--oknodo',
        '--make-pidfile',
        "--pidfile #{chord_java_pidfile_path}",
        '--background',
        "--chdir #{current_path}/../../../ChordJava",
        '--startas /bin/bash',
        "-- -c 'exec java Chord #{node.properties.ip}:#{fetch(:chord_node_port)} > #{chord_java_log_path} 2>&1'"
    end
    
    on roles(:base) do |node|
      execute '/sbin/start-stop-daemon',
        '--start',
        '--quiet',
        '--oknodo',
        '--make-pidfile',
        "--pidfile #{chord_java_pidfile_path}",
        '--background',
        "--chdir #{current_path}/../../../ChordJava",
        '--startas /bin/bash',
        "-- -c 'exec java Chord #{node.properties.ip}:#{fetch(:chord_node_port)} #{root.properties.ip}:#{fetch(:chord_node_port)} > #{chord_java_log_path} 2>&1'"
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
        "--pidfile #{chord_java_pidfile_path}",
        '--background',
        "--chdir #{current_path}/../../../ChordJava",
        '--startas /bin/bash',
        "-- -c 'exec java Chord #{node.properties.ip}:#{fetch(:chord_node_port)} #{known.properties.ip}:#{fetch(:chord_node_port)} > #{chord_java_log_path} 2>&1'"
    end

    # 4. pause to stabilize 8-node ring
    sleep(20)

    # 5. shut down the 4 new nodes
    on roles(:ext) do
      execute '/sbin/start-stop-daemon',
        '--stop',
        '--oknodo',
        "--pidfile #{chord_java_pidfile_path}"
    end

    # 6. pause to stabilize 4-node ring
    sleep(20)

    # 7. stop remaining nodes
    on roles([:root, :base]) do
      execute '/sbin/start-stop-daemon',
        '--stop',
        '--oknodo',
        "--pidfile #{chord_java_pidfile_path}"
    end

  end

  desc 'truncate chord_java log'
  task :truncate_log do
    on roles(:node) do
      execute 'truncate', '-s 0', chord_java_log_path
    end
  end

  desc 'tail chord_java log'
  task :tail_log do
    on roles(:node) do
      execute 'tail', '-n 20', chord_java_log_path
    end
  end

end
