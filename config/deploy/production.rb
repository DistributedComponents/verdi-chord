# server-based syntax
# ======================
# Defines a single server with a list of roles and multiple properties.
# You can define all roles on a single server, or split them:

# server "example.com", user: "deploy", roles: %w{app db web}, my_property: :my_value
# server "example.com", user: "deploy", roles: %w{app web}, other_property: :other_value
# server "db.example.com", user: "deploy", roles: %w{db}

# complete ring
server 'discoberry01.cs.washington.edu', user: 'pi', roles: %w{client},    ip: '128.208.2.23',  name: 'db01'
server 'discoberry02.cs.washington.edu', user: 'pi', roles: %w{node base}, ip: '128.208.2.211', name: 'db02'
server 'discoberry03.cs.washington.edu', user: 'pi', roles: %w{node},      ip: '128.208.2.13',  name: 'db03'
server 'discoberry04.cs.washington.edu', user: 'pi', roles: %w{node base}, ip: '128.208.2.216', name: 'db04'
server 'discoberry05.cs.washington.edu', user: 'pi', roles: %w{node ext},  ip: '128.208.2.214', name: 'db05', known: 'db02'
server 'discoberry06.cs.washington.edu', user: 'pi', roles: %w{node},      ip: '128.208.2.212', name: 'db06'
server 'discoberry07.cs.washington.edu', user: 'pi', roles: %w{node base}, ip: '128.208.2.26',  name: 'db07'
server 'discoberry08.cs.washington.edu', user: 'pi', roles: %w{node ext},  ip: '128.208.2.30',  name: 'db08', known: 'db04'
server 'discoberry09.cs.washington.edu', user: 'pi', roles: %w{node},      ip: '128.208.2.27',  name: 'db09'
server 'discoberry10.cs.washington.edu', user: 'pi', roles: %w{node ext},  ip: '128.208.2.15',  name: 'db10', known: 'db07'

# subset ring
#server 'discoberry01.cs.washington.edu', user: 'pi', roles: %w{node}, name: '23',  succs: %w(13 216),  preds: %w(211), ip: '128.208.2.23'
#server 'discoberry02.cs.washington.edu', user: 'pi', roles: %w{node}, name: '211', succs: %w(23 13),   preds: %w(216), ip: '128.208.2.211'
#server 'discoberry03.cs.washington.edu', user: 'pi', roles: %w{node}, name: '13',  succs: %w(216 211), preds: %w(23),  ip: '128.208.2.13'
#server 'discoberry04.cs.washington.edu', user: 'pi', roles: %w{node}, name: '216', succs: %w(211 23),  preds: %w(13),  ip: '128.208.2.216'

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

set :chord_node_port, 7000
set :chord_serialized_node_port, 8000

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
