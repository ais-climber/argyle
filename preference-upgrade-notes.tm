<TeXmacs|2.1.1>

<style|<tuple|Arxiv|termes-font>>

<\body>
  <doc-data|<doc-title|Preference Upgrade Notes>>

  <section|Neural Network Semantics for Preference Upgrade>

  Here's a sort of \Pto-do\Q list for finding neural semantics for preference
  upgrade operators (and vice-versa, finding classical semantics for neural
  net learning operators). Note that each of the preference upgrade operators
  captures a different interpretation of \Pmake <math|P> more plausible.\Q

  \;

  <\center>
    <tabular|<tformat|<cwith|1|1|1|-1|font-series|bold>|<cwith|1|1|1|-1|cell-tborder|0ln>|<cwith|1|1|1|-1|cell-bborder|1ln>|<cwith|2|2|1|-1|cell-tborder|1ln>|<cwith|1|1|1|1|cell-lborder|0ln>|<cwith|1|1|4|4|cell-rborder|0ln>|<cwith|1|-1|1|-1|cell-lsep|1em>|<cwith|1|-1|1|-1|cell-rsep|1em>|<cwith|1|-1|1|-1|cell-halign|l>|<cwith|2|-1|4|4|cell-hyphen|t>|<cwith|2|-1|3|3|cell-hyphen|t>|<cwith|2|-1|1|-1|cell-bsep|0.3em>|<cwith|2|-1|1|-1|cell-tsep|0.3em>|<table|<row|<cell|Syntax>|<cell|Name>|<cell|Classical
    Semantics>|<cell|Neural Network Semantics>|<cell|Rules>>|<row|<cell|<math|p>>|<cell|Proposition>|<\cell>
      (Fuzzy) Truth Value
    </cell>|<\cell>
      (Fuzzy) Set of neurons
    </cell>|<cell|<with|color|green|<math|\<checkmark\>>>>>|<row|<cell|<math|A\<wedge\>B>>|<cell|Conjunction>|<\cell>
      <math|A> and <math|B>
    </cell>|<\cell>
      <math|A> union <math|B>
    </cell>|<cell|<with|color|green|<math|\<checkmark\>>>>>|<row|<cell|<math|A\<rightarrow\>B>>|<cell|Strict
    Conditional>|<\cell>
      <math|A> strictly implies <math|B> (via <math|\<box\>>)
    </cell>|<\cell>
      <math|graphreach<around*|(|A|)>\<supseteq\>B>
    </cell>|<cell|<with|color|green|<math|\<checkmark\>>>>>|<row|<cell|<math|A\<Rightarrow\>B>>|<cell|Conditional>|<\cell>
      <todo|Todo>
    </cell>|<\cell>
      <math|propagate<around*|(|A|)>\<supseteq\>B>

      (<math|B> is activated by <math|A>)
    </cell>|<cell|<with|font-series|bold|<with|color|purple|?>>>>|<row|<cell|<math|<around*|[|!P|]>A>>|<cell|Public
    Announcement>|<\cell>
      Eliminate all worlds

      where <math|P> is false
    </cell>|<\cell>
      Restrict the graph to <with|font-shape|italic|exactly>

      the set <math|P> (unproven!)
    </cell>|<cell|<with|color|green|<math|\<checkmark\>>>>>|<row|<cell|<math|<around*|[|\<Uparrow\>P|]>A>>|<cell|Lexicographic
    Upgrade>|<\cell>
      Make <math|P> worlds better than

      non-<math|P> worlds
    </cell>|<\cell>
      <with|font-series|bold|<with|color|purple|?>>
    </cell>|<cell|<with|color|green|<math|\<checkmark\>>>>>|<row|<cell|<math|<around*|[|\<uparrow\>P|]>A>>|<cell|Elite
    Upgrade>|<\cell>
      Put the <with|font-shape|italic|most-<math|P>-worlds>

      on top
    </cell>|<\cell>
      <with|font-series|bold|<with|color|purple|?>>
    </cell>|<cell|<with|color|green|<math|\<checkmark\>>>>>|<row|<cell|<math|<around*|[|P|]><rsub|hebb<rsub|U>>A>>|<cell|Unstable
    Hebbian>|<\cell>
      <with|font-series|bold|<with|color|purple|?>>
    </cell>|<\cell>
      Fixed-pt hebbian update
    </cell>|<cell|<with|font-series|bold|<with|color|purple|?>>>>|<row|<cell|<math|<around*|[|P|]><rsub|hebb<rsub|S>>A>>|<cell|Stable
    Hebbian>|<\cell>
      <with|font-series|bold|<with|color|purple|?>>
    </cell>|<\cell>
      Fixed-pt Oja's rule
    </cell>|<cell|<with|font-series|bold|<with|color|purple|?>>>>|<row|<cell|<math|<around*|[|P;Q|]><rsub|backprop>A>>|<cell|Backpropagation>|<\cell>
      <with|font-series|bold|<with|color|purple|?>>
    </cell>|<\cell>
      Fixed-pt backpropagation
    </cell>|<cell|<with|font-series|bold|<with|color|purple|?>>>>>>>
  </center>

  \;

  <section|Polya's Rule of Plausible Inference>

  I was reading George Polya's book <with|font-shape|italic|Patterns of
  Plausible Inference>, where Polya gives a very interesting rule that
  relates plausibility/preference and induction. His rule is the following:

  <\equation*>
    <frac|<tabular|<tformat|<cwith|1|-1|1|1|cell-halign|c>|<table|<row|<cell|A<text|
    implies >B>>|<row|<cell|B<text| true>>>>>>|A<text| more credible>>
  </equation*>

  Compare this to the syllogism we all know:

  <\equation*>
    <frac|<tabular|<tformat|<cwith|1|-1|1|1|cell-halign|c>|<table|<row|<cell|A<text|
    implies >B>>|<row|<cell|B<text| false>>>>>>|A<text| false>>
  </equation*>

  In modern logics of preference upgrade, we can formalize credibility as a
  conditional <math|\<Rightarrow\>>, and \P[make] <math|A> more credible\Q as
  a dynamic modality <math|<around*|[|A|]>> that changes the interpretation
  of the conditional (since the sentence reads like a command). It should be
  fairly straightforward to find a semantics of <math|\<Rightarrow\>> and
  <math|<around*|[|A|]>> that makes this rule sound.

  Why did I mention induction before? Let's say <math|A> and <math|B> are
  actually predicates <math|A<around*|(|x|)>,B<around*|(|x|)>> over instances
  <math|x\<in\>X>. We always have, for any particular <math|t\<in\>X>,

  <\equation*>
    \<forall\>x,A<around*|(|x|)><text| implies >A<around*|(|t|)>
  </equation*>

  If we take this as the first premise of Polya's rule, then we get the
  principle of (plausible) induction:

  <\equation*>
    <frac|<tabular|<tformat|<cwith|1|-1|1|1|cell-halign|c>|<table|<row|<cell|\<forall\>x,A<around*|(|x|)><text|
    implies >A<around*|(|t|)>>>|<row|<cell|A<around*|(|t|)><text|
    true>>>>>>|\<forall\>x,A<around*|(|x|)><text| more credible>>
  </equation*>

  This means that if I can come up with a formal semantics for
  <math|\<Rightarrow\>,<around*|[|A|]>>, and <math|\<forall\>> that makes
  Polya's rule sound, then we get induction for free! (Note:
  <math|\<forall\>> is a bit strong; we might be able to weaken it using
  things like the Universal modality, etc. The important thing here is that a
  theory of plausibility upgrade can give us induction!)

  Since we're going from rules to semantics here, the question is really
  <with|font-shape|italic|which kinds of >semantics make the rule sound (e.g.
  which upgrade operators <math|<around*|[|A|]>> work \V there probably are
  multiple answers to this!)

  <paragraph|Formalizing Polya's Rule.>Polya's inductive rule says that if
  <math|A\<rightarrow\>B> and <math|B> is true, then we should make <math|A>
  more credible. In other words, if we have <math|A\<rightarrow\>B> and
  <math|B>, then any statement <math|C> that holds
  <with|font-shape|italic|after> making <math|A> more plausible
  (<math|<around*|[|A|]>C>) now holds <with|font-shape|italic|anyway> (i.e.
  we can discharge the <math|<around*|[|A|]>>). So our translation into
  dynamic logic is the following:

  <\equation*>
    <frac|A\<rightarrow\>B<space|2em>B<space|2em><around*|[|A|]>C|C>
  </equation*>

  Note that <math|<around*|[|A|]>> doesn't affect \Pground truth\Q
  connectives at all, and so the more interesting case is:

  <\equation*>
    <frac|A\<rightarrow\>B<space|2em>B<space|2em><around*|[|A|]><around*|(|C\<Rightarrow\>D|)>|C\<Rightarrow\>D>
  </equation*>

  I'm going to change the letters to make it clearer what's going on:

  <\equation*>
    <frac|P\<rightarrow\>Q<space|2em>Q<space|2em><around*|[|P|]><around*|(|A\<Rightarrow\>B|)>|A\<Rightarrow\>B>
  </equation*>

  <paragraph|Other Rules.>Polya also suggests two rules that are between the
  demonstrative contrapositive and the inductive rule
  (<with|font-series|bold|shaded contraposition>, and
  <with|font-series|bold|shaded induction>):

  <\equation*>
    <frac|<tabular|<tformat|<cwith|1|-1|1|1|cell-halign|c>|<table|<row|<cell|A<text|
    implies >B>>|<row|<cell|B<text| less credible>>>>>>|A<text| less
    credible>>
  </equation*>

  and

  <\equation*>
    <frac|<tabular|<tformat|<cwith|1|-1|1|1|cell-halign|c>|<table|<row|<cell|A<text|
    implies >B>>|<row|<cell|B<text| more credible>>>>>>|A<text| (somewhat)
    more credible>>
  </equation*>

  Can we express these rules in dynamic modal logic (ignoring the word
  \Psomewhat\Q)? Notice that the second one gives us induction:

  <center|shaded induction <math|\<longrightarrow\>> induction>

  (since <math|A> true <math|\<longrightarrow\>> <math|A> is already made
  more credible)

  <paragraph|The Plan.>

  <\enumerate>
    <item>Translate all of Polya's other rules the same way.

    <item>Go through each of the preference upgrade operators (announcement,
    lexicographic, elite, Hebbian, etc.) and check if they satisfy each of
    the rules. Make a table.

    <item>If <with|font-shape|italic|none> of the operators
    <math|<around*|[|A|]>> satisfy the inductive rules, then I should come up
    with one that does!

    <\itemize>
      <item>Come up with the semantics for a policy that re-orders worlds,
      that satisfies the inductive rules.

      <item>Is this operator reducible to the base language? If so, what's
      the reduction? If not, is there such an operator that
      <with|font-shape|italic|is>, or is this a necessary fact that follows
      from the inductive rules holding?
    </itemize>

    <item>After considering (3), we now have <with|font-shape|italic|some>
    operators <math|<around*|[|A|]>> satisfying the inductive rules. Call
    them <with|font-shape|italic|inductive operators> (or something). These
    are a bridge between preference upgrade and logical induction.

    <\itemize>
      <item>Is there some sort of <with|font-shape|italic|semantic condition>
      that separates which policies are inductive and which aren't?
    </itemize>
  </enumerate>

  \;

  TODO:

  <\enumerate>
    <item>How can I translate the following rule into a logic of preference
    upgrade? (\PA more credible\Q reads like a command.)

    <\equation*>
      <frac|<tabular|<tformat|<cwith|1|-1|1|1|cell-halign|c>|<table|<row|<cell|A<text|
      implies >B>>|<row|<cell|B<text| true>>>>>>|A<text| more credible>>
    </equation*>

    <item>Look through every citation of Polya's book and double-check that
    nobody else has given it formal semantics or related it to KLM
    conditional logics or logics of preference upgrade.
  </enumerate>

  <subsection*|Update:>

  I figured out what preference upgrade operator satisfies Polya's inductive
  rule! It's

  <\equation*>
    <around*|[|A|]>:<text|put all worlds where <with|font-shape|italic|some>
    consequence of >A<text| holds up front>.
  </equation*>

  This is interesting, because in the sense that Elite Upgrade is a
  strengthening of Lexicographic, this <math|<around*|[|A|]>> is a weakening
  of Lexicographic (we put more worlds up front). Does this imply that some
  strengthening of induction holds for Lexicographic and Elite upgrade? Is
  this strengthening closer to the original spirit of induction? (Can this
  analysis help us get at the correct formulation of induction?)

  <section|Supervised Preference Upgrade>

  Say we want to upgrade <math|<around*|[|A\<Rightarrow\>B|]>>, i.e. we want
  to change the model to <with|font-shape|italic|force> the best
  <math|A>-worlds to be <math|B>-worlds. One way to do this is what Rott
  calls \Pbounded revision\Q, which I believe is:\ 

  <\equation*>
    <text|Put all >A<text|-worlds where >B<text| happens to be true up front>
  </equation*>

  Put all <math|A>-worlds where <math|B> happens to be true up front. In the
  resulting model, the best <math|A>-worlds will also be <math|B>-worlds.
  There are variations on this, for example:

  <\equation*>
    <text|Put the <with|font-shape|italic|best> >A<text|-worlds where
    >B<text| happens to be true up front>
  </equation*>

  <\equation*>
    <text|Put the <with|font-shape|italic|best> >A<text|-worlds that happen
    to be <with|font-shape|italic|best> >B<text|-worlds up front>
  </equation*>

  These will also have the intended effect.

  But more interesting is that we can have the same effect by being much more
  conservative in our upgrade: We can restrict our focus only to
  <math|A>-worlds when re-ordering, and just bring the <math|B>-ones (or
  <with|font-shape|italic|best> <math|B>-ones) in front of the rest of the
  <math|A>-worlds. For example:

  <\equation*>
    <text|Put the >A<text|-worlds where >B<text| happens to be true ahead of
    the other <math|A>-worlds (but otherwise preserve the ordering)>
  </equation*>

  Notice that, in contrast with the previous operators, we can't just move
  worlds up-front without consideration of other worlds. Instead, we have to
  consider the overall global state of the ordering when we do the upgrade. I
  suspect that this will correspond to the global effect that backpropagation
  seems to necessarily have.

  It would be nice if I could write down reduction axioms for all of these
  operators, and figure out what corresponding neural network learning
  policies would be.

  \;
</body>

<\initial>
  <\collection>
    <associate|font-base-size|12>
    <associate|math-font|math-termes>
    <associate|page-height|auto>
    <associate|page-medium|paper>
    <associate|page-screen-margin|false>
    <associate|page-type|letter>
    <associate|page-width|auto>
    <associate|par-par-sep|0.3fn>
  </collection>
</initial>

<\references>
  <\collection>
    <associate|auto-1|<tuple|1|1>>
    <associate|auto-2|<tuple|2|1>>
    <associate|auto-3|<tuple|1|2>>
    <associate|auto-4|<tuple|2|2>>
    <associate|auto-5|<tuple|3|3>>
    <associate|auto-6|<tuple|2|?>>
    <associate|auto-7|<tuple|3|?>>
  </collection>
</references>

<\auxiliary>
  <\collection>
    <\associate|toc>
      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|1<space|4spc>Neural
      Network Semantics for Preference Upgrade>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-1><vspace|0.5fn>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|2<space|4spc>Polya's
      Rule of Plausible Inference> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-2><vspace|0.5fn>

      <with|par-left|<quote|4tab>|Formalizing Polya's Rule.
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-3><vspace|0.15fn>>

      <with|par-left|<quote|4tab>|Other Rules.
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-4><vspace|0.15fn>>

      <with|par-left|<quote|4tab>|The Plan.
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-5><vspace|0.15fn>>
    </associate>
  </collection>
</auxiliary>