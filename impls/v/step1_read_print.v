import mal
import readline { read_line }

fn rep_read(input string) !mal.Type {
	return mal.read_str(input)!
}

fn eval(ast mal.Type) mal.Type {
	return ast
}

fn rep_print(ast mal.Type) string {
	return mal.pr_str(ast, true)
}

fn rep(line string) string {
	if ast := rep_read(line) {
		$if ast ? {
			println('AST:\n${ast}')
		}
		return rep_print(eval(ast))
	} else {
		return if err.msg() == 'no form' { '' } else { 'ERROR: ${err}' }
	}
}

fn main() {
	for {
		line := read_line('user> ') or {
			println('')
			break
		}
		out := rep(line)
		if out.len > 0 {
			println(out)
		}
	}
}
