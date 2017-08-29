# server-based syntax
# ======================
# Defines a single server with a list of roles and multiple properties.
# You can define all roles on a single server, or split them:

# server "example.com", user: "deploy", roles: %w{app db web}, my_property: :my_value
# server "example.com", user: "deploy", roles: %w{app web}, other_property: :other_value
# server "db.example.com", user: "deploy", roles: %w{db}

#server 'discoberry01.duckdns.org', user: 'pi', roles: %w{node}, ip: '128.208.7.17',  name: '17',  succs: %w(41 108), preds: %w(155)
#server 'discoberry02.duckdns.org', user: 'pi', roles: %w{node}, ip: '128.208.7.155', name: '155', succs: %w(17 41),  preds: %w(79)
#server 'discoberry03.duckdns.org', user: 'pi', roles: %w{node}, ip: '172.28.7.79',   name: '79',  succs: %w(155 17), preds: %w(99)
#server 'discoberry04.duckdns.org', user: 'pi', roles: %w{node}, ip: '172.28.7.99',   name: '99',  succs: %w(79 155), preds: %w(183)
#server 'discoberry05.duckdns.org', user: 'pi', roles: %w{node}, ip: '128.208.7.183', name: '183', succs: %w(99 79),  preds: %w(91)
#server 'discoberry06.duckdns.org', user: 'pi', roles: %w{node}, ip: '128.208.7.91',  name: '91',  succs: %w(183 99), preds: %w(20)
#server 'discoberry07.duckdns.org', user: 'pi', roles: %w{node}, ip: '128.208.7.20',  name: '20',  succs: %w(91 183), preds: %w(18)
#server 'discoberry08.duckdns.org', user: 'pi', roles: %w{node}, ip: '128.208.7.18',  name: '18',  succs: %w(20 91),  preds: %w(108)
#server 'discoberry09.duckdns.org', user: 'pi', roles: %w{node}, ip: '128.208.7.108', name: '108', succs: %w(18 20),  preds: %w(41)
#server 'discoberry10.duckdns.org', user: 'pi', roles: %w{node}, ip: '128.208.7.41',  name: '41',  succs: %w(108 18), preds: %w(17)

server '128.208.2.23',                   user: 'pi', roles: %w{node}, name: "23", succs: %w(13 216), preds: %w(211), ip: '128.208.2.23'
server 'discoberry02.cs.washington.edu', user: 'pi', roles: %w{node}, name: "211", succs: %w(23 13), preds: %w(216), ip: '128.208.2.211'
server 'discoberry03.cs.washington.edu', user: 'pi', roles: %w{node}, name: "13", succs: %w(216 211), preds: %w(23), ip: '128.208.2.13'
server 'discoberry04.cs.washington.edu', user: 'pi', roles: %w{node}, name: "216", succs: %w(211 23), preds: %w(13), ip: '128.208.2.216'

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
set :make_jobs, 2

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
