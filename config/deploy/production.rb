# server-based syntax
# ======================
# Defines a single server with a list of roles and multiple properties.
# You can define all roles on a single server, or split them:

# server "example.com", user: "deploy", roles: %w{app db web}, my_property: :my_value
# server "example.com", user: "deploy", roles: %w{app web}, other_property: :other_value
# server "db.example.com", user: "deploy", roles: %w{db}

server "db01", roles: %w{node}, host: 'discoberry01.duckdns.org', name: "17", succs: %w(79 99), preds: %w(155), ip: '128.208.7.17'
server "db02", roles: %w{node}, host: 'discoberry02.duckdns.org', name: "155", succs: %w(17 79), preds: %w(99), ip: '128.208.7.155'
server "db03", roles: %w{node}, host: 'discoberry03.duckdns.org', name: "79", succs: %w(99 155), preds: %w(17), ip: '172.28.7.79'
server "db04", roles: %w{node}, host: 'discoberry04.duckdns.org', name: "99", succs: %w(155 17), preds: %w(79), ip: '172.28.7.99'
## server "db05", roles: %w{node}, host: 'discoberry05.duckdns.org', name: "4", adjacent: %w(0 6)
#server "db06", roles: %w{node}, host: 'discoberry06.duckdns.org', name: "5", adjacent: %w(1 9), ip: '128.208.7.91'
## server "db07", roles: %w{node}, host: 'discoberry07.duckdns.org', name: "6", adjacent: %w(4)
#server "db08", roles: %w{node}, host: 'discoberry08.duckdns.org', name: "7", adjacent: %w(1), ip: '128.208.7.18'
## server "db09", roles: %w{node}, host: 'discoberry09.duckdns.org', name: "8", adjacent: %w(6)
#server "db10", roles: %w{node}, host: 'discoberry10.duckdns.org', name: "9", adjacent: %w(5), ip: '128.208.7.41'


# role-based syntax
# ==================

# Defines a role with one or multiple servers. The primary server in each
# group is considered to be the first unless any hosts have the primary
# property set. Specify the username and a domain or IP for the server.
# Don't use `:all`, it's a meta role.

# role :app, %w{deploy@example.com}, my_property: :my_value
# role :web, %w{user1@primary.com user2@additional.com}, other_property: :other_value
# role :db,  %w{deploy@example.com}



# Configuration
# =============
# You can set any configuration variable like in config/deploy.rb
# These variables are then only loaded and set in this stage.
# For available Capistrano configuration variables see the documentation page.
# http://capistranorb.com/documentation/getting-started/configuration/
# Feel free to add new variables to customise your setup.

set :node_port, 7000

# Custom SSH Options
# ==================
# You may pass any option but keep in mind that net/ssh understands a
# limited set of options, consult the Net::SSH documentation.
# http://net-ssh.github.io/net-ssh/classes/Net/SSH.html#method-c-start
#
# Global options
# --------------
#  set :ssh_options, {
#    keys: %w(/home/rlisowski/.ssh/id_rsa),
#    forward_agent: false,
#    auth_methods: %w(password)
#  }
#
# The server-based syntax can be used to override options:
# ------------------------------------
# server "example.com",
#   user: "user_name",
#   roles: %w{web app},
#   ssh_options: {
#     user: "user_name", # overrides user setting above
#     keys: %w(/home/user_name/.ssh/id_rsa),
#     forward_agent: false,
#     auth_methods: %w(publickey password)
#     # password: "please use keys"
#   }