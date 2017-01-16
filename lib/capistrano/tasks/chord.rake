namespace :chord do
  
  desc 'start chord'
  task :start do
    servers = Hash[roles(:node).collect { |s| [s.properties.name, s] }]
    on roles(:node) do |server|
      preds = server.properties.preds.collect { |s| "-pred #{servers[s].properties.ip}:#{fetch(:node_port)}" }.join(' ')
      succs = server.properties.succs.collect { |s| "-succ #{servers[s].properties.ip}:#{fetch(:node_port)}" }.join(' ')
      execute '/sbin/start-stop-daemon',
        '--start',
        '--quiet',
        '--oknodo',
        '--make-pidfile',
        "--pidfile #{current_path}/extraction/chord/tmp/chord.pid",
        '--background',
        "--chdir #{current_path}/extraction/chord",
        '--startas /bin/bash',
        "-- -c 'exec ./chord.native -bind #{server.properties.ip}:#{fetch(:node_port)} #{preds} #{succs} > log/chord.log 2>&1'"
    end
  end

  desc 'stop chord'
  task :stop do
    on roles(:node) do
      execute '/sbin/start-stop-daemon', 
        '--stop',
        '--oknodo',
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
