use v6;
subset Nat of Int where * ≥ 0;
role Sym {}

class Terminal does Sym {
    has $.token is required;
    has Nat $.from;
    has Nat $.to;
    method gist(--> Str) {
        return $.from.defined && $.to.defined
            ?? "$.from⋯$.to ❰$.token❱"
            !! "❰$.token❱";
    }
}

class Regular-Token is Terminal { }

subset Nonterminal-Name of Str where .chars > 0;
class Nonterminal does Sym {
    has Nonterminal-Name $.name is required;
    has Nat $.from;
    has Nat $.to;
    has $.tree is rw;
    method gist(--> Str) {
        return $.from.defined && $.to.defined && $.tree.defined
            ?? "$.from⋯$.to $.name { $.tree.gist }"
            !! "$.name";
    }
}

class Rule {
    has Nonterminal-Name $.name is required;
    has Sym @.sym is required;
    has Callable @.action;
    method clone { nextwith :sym(@!sym.clone), |%_ }
    method gist(--> Str) {
        return '%s → %s'.sprintf: $.name, @.sym.map(*.gist).join: ' ';
    }
}

class Grammar {
    has Nonterminal-Name $.start = @!rules[0].name;
    has Rule @.rules is required;
    # FIXME this should be an "is cached" method
    method nullable(--> Set) { # FIXME Set[Nonterminal-Name] RT#133762
        my %nullable = SetHash.new; # FIXME SetHash[Nonterminal-Name] RT#133762
        my Nat $old-size = 0;
        repeat {
            $old-size = %nullable.elems;
            for @!rules -> $rule {
                next if $rule.sym.first: -> $sym {
                    $sym ~~ Terminal || %nullable{$sym.name}.not
                };
                %nullable{$rule.name}++;
            }
        } until $old-size == %nullable.elems;
        return %nullable.Set;
    };
    our sub rules-from-ebnf(@ebnf) {
        return gather {
            for @ebnf -> $rule {
                my (@sym, @action);
                for $rule.sym.kv -> $sym-idx, $sym {
                    if $sym ~~ Regular-Token {
                        my @new-sym = $sym.token.comb.map(-> $token {
                            Terminal.new: :$token;
                        }).Slip;
                        @sym.push: @new-sym.Slip;
                        @action.push:
                            sub ($i, @v) {
                                @v.map: -> $v {
                                    my @sym = $v.tree[];
                                    @sym.splice: $sym-idx, @new-sym.elems, Regular-Token.new(
                                        from => $v.tree[$sym-idx].from,
                                        to => $v.tree[$sym-idx + @new-sym.elems - 1].to,
                                        token => $v.tree[$sym-idx ..^ $sym-idx + @new-sym.elems].map(*.token).join
                                    );
                                    $v.tree = @sym;
                                    $v
                                }
                            };
                    } else {
                        @sym.push: $sym;
                    }
                }
                take $rule.clone(:@sym, :@action);
            }
        }
    }
}

enum Reason <completion nullable-prediction prediction reduction-path scanner seed>;
subset Span of Pair where $_.key ~~ Int && $_.value ~~ Int && 0 ≤ $_.key ≤ $_.value;
class Item {
    has Rule $.rule is required;
    has Nat $.from is required;
    has Nat $.to is rw;
    has Nat $.dot is required;
    has Reason $.reason is required;
    has Span @.spans;
    has @.scans;
    method gist(--> Str) {
        my $out;
        $out ~= $.to
            ?? '(from %2d to %2d) '.sprintf: $.from, $.to
            !! '(from %2d) '.sprintf: $.from;
        $out ~= '%s →'.sprintf: $.rule.name;
        for $.rule.sym.kv -> $idx, $sym {
            $out ~= $.dot == $idx ?? ' • ' !! ' ';
            $out ~= $sym.gist;
        }
        $out ~= ' ●' if $.dot == $.rule.sym.elems;
        $out ~= ' |%s| '.sprintf: $.reason;
        $out ~= @.spans.gist;
        $out ~= @.scans.gist;
        return $out;
    }
}

subset Predicted-Terminal of Pair where $_.key ~~ Terminal && $_.value ~~ Item;
class Result {
    has Bool $.success is required;
    has Nat $.position is required;
    has @.results;
    has Predicted-Terminal @.predicted;
}

class Parser {
    has Grammar $.grammar is required;
    has Array[Item] @.chart;
    has &.nonterminal-value = sub ($item, $tree) {
        return Nonterminal.new:
            name => $item.rule.name,
            from => $item.from,
            to => $item.to,
            tree => $tree,
        ;
    };
    has &.terminal-value = sub ($item, $idx, $sym) {
        return Terminal.new:
            token => $sym.token,
            from => $item.spans[$idx].key,
            to => $item.spans[$idx].value,
        ;
    };
    has &.scan = sub (:$input, Nat :$position) {
        return $input.substr($position, 1) || Nil;
    };
    has &.match = sub (Terminal :$terminal, :$scan, Nat :$position --> Bool) {
        return $scan eq $terminal.token;
    };
    method append(Item @items, Item $item) {
        return if @items.first: -> $i {
            $i.rule eq $item.rule &&
            $i.from == $item.from &&
            $i.dot == $item.dot &&
            $i.spans ~~ $item.spans
        };
        @items.push: $item;
    }
    method reduction-path(Item :$item, Item :@reduction-path --> Array[Item]) {
        my @path = @.chart[$item.from].grep: -> $i {
            ($i.dot + 1 == $i.rule.sym.elems) &&
            $i.rule.sym.elems.so &&
            ($item.rule.name eq $i.rule.sym[* - 1].name) &&
            ($i.from != $item.from)
        };
        if 1 == @path.elems {
            @reduction-path.unshift: @path[0];
            self.reduction-path:
                item => @path[0],
                reduction-path => @reduction-path
            ;
        } else {
            return @reduction-path;
        }
    }
    method admit(:$input, Bool :$with-spans = False --> Result) {
        for $.grammar.rules -> $rule {
            if $rule.name eq $.grammar.start {
                @.chart[0].push: Item.new:
                    rule => $rule,
                    from => 0,
                    dot => 0,
                    reason => seed,
                ;
            }
        }
        my $i = 0;
        while ($i < @.chart.elems) {
            my $j = 0;
            while ($j < @.chart[$i].elems) {
                my $item = @.chart[$i;$j];
                my $symbol = $item.rule.sym[$item.dot];
                given $symbol {
                    when Sym:U {
#                         FIXME bug #2
#                         my @reduction-path = self.reduction-path(:$item);
#                         if @reduction-path.elems {
#                             self.append: @.chart[$i], Item.new:
#                                 rule => @reduction-path[0].rule,
#                                 from => @reduction-path[0].from,
#                                 dot => @reduction-path[0].dot + 1,
#                                 reason => reduction-path,
#                             ;
#                             next;
#                         }
                        for |@.chart[$item.from] -> $old-item {
                            my $next-symbol = $old-item.rule.sym.[$old-item.dot];
                            next if $next-symbol ~~ Sym:U;
                            if (
                                $next-symbol ~~ Nonterminal &&
                                $next-symbol.name eq $item.rule.name
                            ) {
                                my $new-item = Item.new(
                                    rule => $old-item.rule,
                                    from => $old-item.from,
                                    dot => $old-item.dot + 1,
                                    reason => completion,
                                    spans => $old-item.spans,
                                    scans => $old-item.scans,
                                );
                                # FIXME bug #1
#                                 if ($with-spans) {
#                                     $new-item.spans.[$new-item.dot - 1] =
#                                         1 == $new-item.dot
#                                         ?? [$new-item.from, $i]
#                                         !! [
#                                             $new-item.spans.[$new-item.dot - 2;1],
#                                             $i
#                                         ];
#                                 }
                                self.append: @.chart[$i], $new-item;
                            }
                        }
                    }
                    when Terminal:D {
                        my $scan = self.scan.(:$input, position => $i);
                        if $scan.defined && self.match.(
                            terminal => $symbol, position => $i, :$scan
                        ) {
                            my $new-item = Item.new:
                                rule => $item.rule,
                                from => $item.from,
                                dot => $item.dot + 1,
                                reason => scanner,
                                spans => $item.spans,
                                scans => $item.scans,
                            ;
                            if $with-spans {
                                $new-item.spans[$item.dot] = $i => $i + 1;
                                $new-item.scans[$item.dot] = $scan;
                            }
                            @.chart[$i + 1].push: $new-item;
                        }
                    }
                    when Nonterminal:D {
                        for $.grammar.rules -> $rule {
                            if $rule.name eq $symbol.name {
                                self.append: @.chart[$i], Item.new:
                                    rule => $rule,
                                    dot => 0,
                                    from => $i,
                                    reason => prediction,
                                ;
                                self.append(@.chart[$i], Item.new:
                                    rule => $item.rule,
                                    from => $item.from,
                                    dot => $item.dot + 1,
                                    reason => nullable-prediction,
                                    spans => $item.spans,
                                    scans => $item.scans,
                                ) if $.grammar.nullable{$rule.name}:exists;
                            }
                        }
                    }
                    default { die }
                }
                NEXT { $j++ }
            }
            $i++;
        }
        if @.chart[* - 1].grep(-> $item {
            0 == $item.from &&
            $item.dot == $item.rule.sym.elems &&
            $.grammar.start eq $item.rule.name
        }) {
            return Result.new: :success, position => $i - 1;
        } else {
            return Result.new:
                :!success,
                position => $i - 1,
                predicted => @.chart[* - 1].grep(-> $item {
                    $item.dot != $item.rule.sym.elems &&
                    $item.rule.sym[$item.dot] ~~ Terminal
                }).map(-> $item {
                    ($item.rule.sym[$item.dot] => $item)
                });
        }
    }
    method complete-spans {
        # FIXME bug #1
        sub span-slices(Int $parts where * > 0, Span $span) {
            return 1 == $parts
                ?? (($span,),)
                !! gather {
                    for $span.key .. $span.value -> $outer {
                        for span-slices($parts - 1, $outer => $span.value) -> $inner {
                            take ($span.key => $outer, |$inner);
                        }
                    }
                }
        };
        sub prev-span($item, $idx) {
            return 0 == $idx ?? $item.from !!
                $item.spans[$idx - 1].defined ?? $item.spans[$idx - 1].value !! $item.spans[$idx - 1];
        }
        sub succ-span($item, $idx) {
            return $item.rule.sym.elems - 1 == $idx ?? $item.to !!
                $item.spans[$idx + 1].defined ?? $item.spans[$idx + 1].key !! $item.spans[$idx + 1];
        }
        my @complete = gather {
            for @.chart.kv -> $i, @set {
                for @set -> $item {
                    my $syms = $item.rule.sym.elems;
                    if $item.dot == $syms {
                        $item.to = $i;
                        { # fill single gaps
                            for $item.rule.sym.kv -> $idx, $sym {
                                next if $item.spans[$idx].defined;
                                next unless prev-span($item, $idx).defined;
                                next unless succ-span($item, $idx).defined;
                                $item.spans[$idx] = prev-span($item, $idx) => succ-span($item, $idx);
                            }
                        }
                        if (
                            $syms == $item.spans.elems &&
                            $syms == $item.spans.grep: *.defined
                        ) {
                            take $item;
                        } else {
                            FILL:
                            for span-slices($syms, ($item.from => $item.to)) -> @filled {
                                for ^$syms -> $idx {
                                    my $span = $item.spans[$idx];
                                    next unless $span.defined;
                                    my $filled-span = @filled[$idx];
                                    next FILL unless
                                        $filled-span.key == $span.key &&
                                        $filled-span.value == $span.value;
                                }
                                my @s;
                                for ^$syms -> $idx {
                                    @s[$idx] = $item.spans[$idx] // @filled[$idx];
                                }
                                take Item.new:
                                    rule => $item.rule,
                                    from => $item.from,
                                    to => $item.to,
                                    dot => $item.dot,
                                    reason => $item.reason,
                                    spans => @s,
                                    scans => $item.scans,
                                ;
                            }
                        }
                    }
                }
            }
        }
        return @complete.grep(-> $item {
            my $ok = True;
            for $item.rule.sym.kv -> $idx, $sym {
                if $sym ~~ Nonterminal {
                    $ok = False unless @complete.first: -> $i {
                        $i.rule.name eq $sym.name &&
                        $i.from == $item.spans[$idx].key &&
                        $i.to == $item.spans[$idx].value
                    }
                }
            }
            $ok
        });
    }
    method tree($item, @completed) {
        return self.nonterminal-value.($item, Any)
            if 0 == $item.rule.sym.elems;
        my %subtrees;
        for @completed -> $i {
            for $item.rule.sym.kv -> $idx, $sym {
                if
                    $sym ~~ Nonterminal &&
                    $i.rule.name eq $sym.name &&
                    $i.from == $item.spans[$idx].key &&
                    $i.to == $item.spans[$idx].value
                {
                    my $key = '%s_%d_%d'.sprintf: $i.rule.name, $i.from, $i.to;
                    my @x = self.tree($i, @completed);
                    %subtrees{$key}.push: |@x;
                };
            }
        }
        my @values = gather {
            for $item.rule.sym.kv -> $idx, $sym {
                given $sym {
                    when Terminal {
                        take self.terminal-value.($item, $idx, $sym);
                    }
                    when Nonterminal {
                        my $key = '%s_%d_%d'.sprintf: $sym.name,
                            $item.spans[$idx].key, $item.spans[$idx].value;
                        take %subtrees{$key};
                    }
                    default { die }
                }
            }
        }
        @values = (
            # FIXME https://github.com/rakudo/rakudo/issues/2016
            1 == @values.elems ?? cross(@values[0],) !! cross(@values.List)
        ).map: -> $tree { self.nonterminal-value.($item, $tree) };
        if $item.rule.action {
            for $item.rule.action -> $action {
                @values = $action.($item, @values)
            }
        }
        return @values;
    };
    method parse(:$input --> Result) {
        my $r = self.admit(:$input, with-spans => True);
        return $r unless $r.success;
        my @completed = self.complete-spans;
        my @end = @completed.grep: -> $item {
            0 == $item.from &&
            @.chart.elems - 1 == $item.to &&
            $.grammar.start eq $item.rule.name
        };
        @end = @.chart[* - 1].grep: -> $item {
            0 == $item.from &&
            $item.dot == $item.rule.sym.elems &&
            $.grammar.start eq $item.rule.name
        } unless @end;
        $r.results = @end.map(-> $item { self.tree: $item, @completed }).flat;
        return $r;
    }
    method gist(Bool $only_complete = False --> Str) {
        my $out = '';
        for @.chart.kv -> $i, @items {
            $out ~= "=== $i ===\n";
            for @items.kv -> $j, $item {
                next if $only_complete && $item.dot != $item.rule.sym.elems;
                $out ~= '[%2d][%2d] '.sprintf: $i, $j;
                $out ~= $item.gist ~ "\n";
            }
        }
        return $out;
    }
}

=begin pod

bug #1: record the spans in the completion step instead of filling them in
after recognising is finished

bug #2: calculate the set of right recursion rules and add the reduction
path only when completing a right recursive rule

bug #3: better return values when recognising fails, when input is left over

bug #4: add logging/tracing

bug #5: visualise with GFG

bug #6: directly handle regular right sides

bug #7: find opportunities to autothread map over arrays

bug #8: show where the ambiguity originates

bug #9: sanity check cyclic grammars

bug #10: generate random sentences from a grammar

bug #11: formalise the mechanism for transforming natural rules into synthetic

bug #12: in error messages, show the natural rules, not the synthetic rules

bug #13: steal synalysis XML grammars

bug #14: put some sane limits into the parser: number of rules

=end pod
