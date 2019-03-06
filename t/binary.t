use v6;
use Zuversicht;
use Test;

sub T($token) { Terminal.new: :$token }
sub N(Str $name) { Nonterminal.new: :$name }
sub R(Pair $p) { Rule.new: :name($p.key) :sym($p.value) }
sub G($rules) { Grammar.new: rules => $rules.map(-> $r { R $r }) }

my $grammar = G (d
    S => (T(Blob.new(0)), T(Blob.new(1)), T(Blob.new(2))),
);
my $input = "\x0\x1\x2".encode;
my $parser = Parser.new(
    :$grammar,
    scan => sub (:$input, Nat :$position) {
        return $input[$position] // Nil;
    },
    match => sub (Terminal :$terminal, :$scan, Nat :$position --> Bool) {
        return $scan == $terminal.token.read-uint8(0);
    },
    terminal-value => sub ($item, $idx, $sym) {
        return $item.scans[$idx];
    },
    nonterminal-value => sub ($item, $l) {
        return $item.rule.name, $l.Slip;
    },
);
my $result = $parser.parse(:$input);
ok $result.success, 'type';
is $result.position, 3, 'position';
is $result.results, [<S 0 1 2>], 'results';
