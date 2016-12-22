namespace :chord do
  
  desc 'start chord'
  task :start do
    cluster = roles(:node).collect { |s| "-node #{s.properties.node_name},#{s.hostname}:#{fetch(:node_port)}" }.join(' ')
    on roles(:node) do |server|
      execute '/sbin/start-stop-daemon',
        '--start',
        '--quiet',
        '--make-pidfile',
        "--pidfile #{current_path}/extraction/chord/tmp/chord.pid",
        '--background',
        "--chdir #{current_path}/extraction/chord",
        '--startas /bin/bash',
        "-- -c \"exec ./chord.native -me #{server.properties.node_name} -port #{server.properties.client_port} #{cluster} > log/chord.log 2>&1\""
    end
  end

  desc 'stop chord'
  task :stop do
    on roles(:node) do
      execute '/sbin/start-stop-daemon', 
        '--stop',
        "--pidfile #{current_path}/extraction/chord/tmp/chord.pid"
    end
  end

  desc 'tail chord log'
  task :tail_log do
    on roles(:node) do
      execute 'tail',
        '-n 20',
        "#{shared_path}/extraction/chord/log/chord.log"
    end
  end

  desc 'truncate chord log'
  task :truncate_log do
    on roles(:node) do
      execute 'truncate',
        '-s 0',
        "#{shared_path}/extraction/chord/log/chord.log"
    end
  end

end
