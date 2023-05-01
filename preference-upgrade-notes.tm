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

      the set <math|P>
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
    </cell>|<cell|<with|color|green|<math|\<checkmark\>>>>>|<row|<cell|<math|<around*|[|P|]><rsub|hebb<rsub|S>>A>>|<cell|Stable
    Hebbian>|<\cell>
      <with|font-series|bold|<with|color|purple|?>>
    </cell>|<\cell>
      Fixed-pt Oja's rule
    </cell>|<cell|<with|font-series|bold|<with|color|purple|?>>>>|<row|<cell|<math|<around*|[|P|]><rsub|backprop>A>>|<cell|Backpropagation>|<\cell>
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
  conditional <math|\<Rightarrow\>>, and \P<math|A> more credible\Q as a
  dynamic modality <math|<around*|[|A|]>> that changes the interpretation of
  the conditional. It should be fairly straightforward to find a semantics of
  <math|\<Rightarrow\>> and <math|<around*|[|A|]>> that makes this rule
  sound.

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

  <paragraph|Formalizing Polya's Rule.>How do we faithfully translate Polya's
  rule? That depends on how we interpret the dynamics of \P[make] <math|A>
  more credible.\Q

  <\equation*>
    <frac|<around*|(|<frac|A\<rightarrow\>B<space|2em>B|C>|)>|<around*|[|A|]>C>
  </equation*>

  <\equation*>
    <around*|(|<around*|(|<around*|(|A\<rightarrow\>B|)>\<wedge\>B|)>\<rightarrow\>C|)>\<rightarrow\><around*|[|A|]>C
  </equation*>

  ???
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
    <associate|auto-1|<tuple|1|1|../../.TeXmacs/texts/scratch/no_name_11.tm>>
    <associate|auto-2|<tuple|2|?|../../.TeXmacs/texts/scratch/no_name_11.tm>>
    <associate|auto-3|<tuple|1|?|../../.TeXmacs/texts/scratch/no_name_11.tm>>
  </collection>
</references>

<\auxiliary>
  <\collection>
    <\associate|toc>
      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|1<space|4spc>Neural
      Network Semantics for Preference Upgrade>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-1><vspace|0.5fn>
    </associate>
  </collection>
</auxiliary>