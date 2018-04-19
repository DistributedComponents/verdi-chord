namespace :chord_serialized do

  def chord_serialized_log_path
    "#{shared_path}/extraction/chord-serialized/log/chord-serialized.log"
  end

  def chord_serialized_pidfile_path
    "#{shared_path}/extraction/chord-serialized/tmp/chord-serialized.pid"
  end

  desc 'start serialized chord'
  task :start do
    nodes = Hash[roles(:node).collect { |node| [node.properties.name, node] }]
    on roles(:node) do |node|
      preds = node.properties.preds.collect { |n| "-ring #{nodes[n].properties.ip}:#{fetch(:chord_serialized_node_port)}" }.join(' ')
      succs = node.properties.succs.collect { |n| "-ring #{nodes[n].properties.ip}:#{fetch(:chord_serialized_node_port)}" }.join(' ')
      execute '/sbin/start-stop-daemon',
        '--start',
        '--quiet',
        '--oknodo',
        '--make-pidfile',
        "--pidfile #{chord_serialized_pidfile_path}",
        '--background',
        "--chdir #{current_path}/extraction/chord-serialized",
        '--startas /bin/bash',
        "-- -c 'exec ./chordserialized.native -bind #{node.properties.ip}:#{fetch(:chord_serialized_node_port)} #{preds} #{succs} > log/chord-serialized.log 2>&1'"
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

end
