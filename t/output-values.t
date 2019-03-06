use v6;
use Zuversicht;
use Test;

sub T($token) { Terminal.new: :$token }
sub N(Str $name) { Nonterminal.new: :$name }
sub R(Pair $p) { Rule.new: :name($p.key) :sym($p.value) }
sub G($rules) { Grammar.new: rules => $rules.map(-> $r { R $r }) }
my $grammar = G (
    S => (T('a'), T('b'), T('c')),
);

{
    my $input = 'abc';
    my $parser = Parser.new(
        :$grammar,
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
    is $result.results, [<S a b c>], 'results';
}
{
    my $input = 'ab';
    my $parser = Parser.new(
        :$grammar,
        terminal-value => sub ($item, $idx, $sym) {
            return $item.scans[$idx];
        },
        nonterminal-value => sub ($item, $l) {
            return $item.rule.name, $l.Slip;
        },
    );
    my $result = $parser.parse(:$input);
    ok !$result.success, 'type';
    is $result.position, 2, 'position';
    is $result.predicted[0].key.token, 'c', 'predicted';
}
