BEGIN {
  FS = ","
  if(commit == "") {
    commit = "master"
  }
  gh = "https://github.com/DistributedComponents/verdi-chord/blob/" commit
}

{
  if (NR == 1) {
    print $0
  } else {
    printf("<a href='%s/%s'>%s</a>,%s\n", gh, $1, $1, $2)
  }
}
