theory VC_To_HC
  imports  Main "Three_Sat_To_Set_Cover" Graph_Theory.Graph_Theory
begin

subsection\<open>Preliminaries\<close>

definition
  "is_vertex_cover_list E V \<equiv> \<forall> e \<in> set E. \<exists> v \<in> set V. v \<in> e"

(*If size of V is smaller than k, then there is a problem concerning the cover nodes in the Graph*)
definition
  "vertex_cover_list \<equiv>
  {(E, k). \<exists>V. ugraph (set E) \<and> (set V) \<subseteq> \<Union> (set E) \<and> k \<le> card (\<Union> (set E)) \<and> size V = k \<and> 
    is_vertex_cover_list E V \<and> distinct E \<and> distinct V}"

datatype ('a, 'b) hc_node = Cover nat | Edge 'a 'b nat

(*pre_digraph.cycle already assumes that every node is only contained once*)
(*Case for empty c is already in cycle*)
definition
  "is_hc (G::('a,('a \<times> 'a)) pre_digraph) (c:: 'a list)  \<equiv> 
    (pre_digraph.cycle G (vwalk_arcs c) \<and> (\<forall>x\<in> verts G. x \<in> set c))\<or> card (verts G) \<le> 1"

definition
  "hc \<equiv> {G. \<exists>c. wf_digraph G \<and> is_hc G c}"

definition
  "vc_hc \<equiv> \<lambda>(E, k).
    if ugraph (set E) \<and>  k \<le> card (\<Union> (set E))
        then  \<lparr>verts = {Cover i|i. i< k} \<union> {Edge v e 0|v e. e\<in> set E \<and> v \<in> e}\<union> {Edge v e 1|v e. e\<in> set E \<and> v \<in> e},
          arcs = {(Edge v e 0, Edge v e 1)|v e. e\<in> set E \<and> v \<in> e} \<union> 
            {(Edge v e 0, Edge u e 0)|u v e. e\<in>set E \<and> v \<in> e \<and> u \<in> e} \<union>
            {(Edge v e 1, Edge u e 1)|u v e. e\<in> set E \<and> v \<in> e \<and> u \<in> e} \<union>
            {(Edge v e1 1, Edge v e2 0)| v e1 e2 i j. i<length E \<and> j<length E \<and>  e1 = E!i\<and> e2 = E!i \<and> v \<in> e1 \<and> v \<in> e2 \<and> 
              \<not> (\<exists>i'< size E. v \<in> E!i' \<and> i < i' \<and> i' < j)} \<union>
            {(Edge v e 1, Cover n)| v e n i. i<length E \<and> e = E!i\<and> v \<in> e \<and> 
              \<not> (\<exists>j < size E. v \<in> E!j \<and> i < j) \<and> n< k}\<union>
            {(Cover n, Edge v e 0)| v e n i. i<length E \<and> e = E!i\<and> v \<in> e \<and> 
              \<not> (\<exists>j < size E. v \<in> E!j \<and> j < i) \<and> n < k},
          tail = fst, head = snd \<rparr>
        else \<lparr>verts = {Cover 0}, arcs = {}, tail = fst, head = snd\<rparr>"


lemma else_not_in_hc: 
  assumes "G = \<lparr>verts = {Cover 0, Cover 1}, arcs = {}, tail = fst, head = snd\<rparr>"
  shows "G \<notin> hc"
proof 
  assume "G \<in> hc"
  then have "\<exists> c. pre_digraph.cycle G (vwalk_arcs c) \<and> (\<forall>x\<in> verts G. x \<in> set c)" 
    using assms hc_def 
    by (simp add: hc_def doubleton_eq_iff is_hc_def)
  then obtain c where c_def: "pre_digraph.cycle G (vwalk_arcs c)" "(\<forall>x\<in> verts G. x \<in> set c)" by blast
  with pre_digraph.cycle_def have not_empty: "vwalk_arcs c \<noteq> []"  by fastforce
  from pre_digraph.cycle_def pre_digraph.awalk_def c_def have subset: "set (vwalk_arcs c) \<subseteq> arcs G" by metis
  have "arcs G = {}" using assms by(auto)
  with subset  have "set (vwalk_arcs c) = {}" by auto
  then show "False" using not_empty by(auto)
qed

lemma else_wf_digraph: 
  assumes "G = \<lparr>verts = {Cover 0, Cover 1}, arcs = {}, tail = fst, head = snd\<rparr>"
  shows "wf_digraph G"
  by(auto simp add: hc_def wf_digraph_def is_hc_def assms)

lemma if_else_in_hc: 
  assumes "G = \<lparr>verts = {Cover 0}, arcs = {}, tail = fst, head = snd\<rparr>"
  shows "G \<in> hc"
  by(auto simp add: hc_def wf_digraph_def is_hc_def assms)

lemma if_else_wf_digraph: 
  assumes "G = \<lparr>verts = {Cover 0}, arcs = {}, tail = fst, head = snd\<rparr>"
  shows "wf_digraph G"
  by(auto simp add: hc_def wf_digraph_def is_hc_def assms)

lemma card_greater_1_contains_two_elements:
  assumes "card S > 1"
  shows "\<exists>u v. v\<in> S \<and> u\<in> S \<and> u \<noteq> v"
proof -
  have "S \<noteq> {}"
    using assms by(auto)
  then have "\<exists>v. v \<in> S" by(auto)
  then obtain v where "v \<in> S" by auto 
  have "(S-{v}) \<noteq> {}" 
    using assms
    by (metis Diff_empty Diff_idemp Diff_insert0 \<open>S \<noteq> {}\<close> card.insert_remove card_empty finite.emptyI insert_Diff less_Suc0 less_numeral_extra(4) less_one)
  then have "\<exists>u. u \<in> S-{v}" 
    by(auto)
  then obtain u where "u\<in> S-{v}"
    by auto
  then have "u\<in> S" by(auto)
  then have "u \<noteq> v" using \<open>u\<in>S-{v}\<close> by(auto)
  then show ?thesis using \<open>u\<in> S\<close> \<open>v \<in> S\<close> by auto
qed

lemma contains_two_card_greater_1:
  assumes "v \<in> S" "u \<in> S" "u \<noteq> v" "finite S"
  shows "1 < card S"
using assms apply(auto) 
  by (meson card_le_Suc0_iff_eq not_le_imp_less) 

subsection\<open>(E,k) \<in> vc \<Longrightarrow> vc_hc (E, k) f \<in> hc\<close>

definition get_second where
  "get_second e \<equiv> SOME v. v \<in> e"

lemma edge_contains_minus_one_not_empty: 
  assumes "e \<in> set E'" "ugraph (set E')" "u \<in> e"
  shows "e-{u} \<noteq> {}"
using subset_singletonD assms ugraph_def by fastforce

lemma ugraph_implies_smaller_set_ugraph:
  assumes "ugraph (insert a (set E'))"
  shows "ugraph (set E')"
  using assms by (simp add: ugraph_def)

lemma get_second_in_edge:
  assumes "u = get_second e" "e \<noteq> {}"
  shows "u \<in> e"
  using assms unfolding  get_second_def apply(auto) 
  using some_in_eq by auto

fun construct_cycle_add_edge_nodes:: "('a set list) \<Rightarrow> 'a \<Rightarrow> ('a set) \<Rightarrow>  (('a, 'a set) hc_node) list"
  where 
"construct_cycle_add_edge_nodes [] v C = []" |
"construct_cycle_add_edge_nodes (e#es) v C = (if v \<in> e then 
    (let u = (get_second (e-{v})) in 
      (if u\<in> C then [(Edge v e 0), (Edge v e 1)] 
      else [(Edge v e 0), (Edge u e 0), (Edge u e 1), (Edge v e 1)])) @ construct_cycle_add_edge_nodes es v C 
    else construct_cycle_add_edge_nodes es v C)"

fun construct_cycle_1::"'a set list \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> 'a set \<Rightarrow> (('a, 'a set) hc_node) list"  where
"construct_cycle_1 E (x#Cs) n C =(Cover n) # (construct_cycle_add_edge_nodes E x C) @ 
    (construct_cycle_1 E Cs (n+1) C)"|
"construct_cycle_1 E [] n C = [(Cover 0)]"

fun construct_cycle:: "'a set list \<Rightarrow> 'a list \<Rightarrow> (('a, 'a set) hc_node \<times> ('a, 'a set) hc_node) list" where
"construct_cycle E C = vwalk_arcs (construct_cycle_1 E C 0 (set C))"


context 
  fixes E k assumes in_vc: "(E, k) \<in> vertex_cover_list"
  fixes Cov assumes Cov_def:"is_vertex_cover_list E Cov" "distinct Cov" "size Cov = k"
  fixes G assumes G_def: "G = vc_hc (E,k)"
  fixes Cycle assumes Cycle_def: "Cycle = construct_cycle_1 E Cov 0 (set Cov)"
begin

lemma "size Cov = card (set Cov)"
  using Cov_def by (simp add: distinct_card)

lemma in_vc_k_smaller:
  assumes "(E, k) \<in> vertex_cover_list" "\<not> k \<le> card (\<Union> (set E))"
  shows "False"
  using vertex_cover_list_def assms by(auto simp add: vertex_cover_list_def assms)

lemma G_def_2:
  shows "G =  \<lparr>verts = {Cover i|i. i< k} \<union> {Edge v e 0|v e. e\<in> set E \<and> v \<in> e}\<union> {Edge v e 1|v e. e\<in> set E \<and> v \<in> e},
          arcs = {(Edge v e 0, Edge v e 1)|v e. e\<in> set E \<and> v \<in> e} \<union> 
            {(Edge v e 0, Edge u e 0)|u v e. e\<in>set E \<and> v \<in> e \<and> u \<in> e} \<union>
            {(Edge v e 1, Edge u e 1)|u v e. e\<in> set E \<and> v \<in> e \<and> u \<in> e} \<union>
            {(Edge v e1 1, Edge v e2 0)| v e1 e2 i j. i<length E \<and> j<length E \<and>  e1 = E!i\<and> e2 = E!i \<and> v \<in> e1 \<and> v \<in> e2 \<and> 
              \<not> (\<exists>i'< size E. v \<in> E!i' \<and> i < i' \<and> i' < j)} \<union>
            {(Edge v e 1, Cover n)| v e n i. i<length E \<and> e = E!i\<and> v \<in> e \<and> 
              \<not> (\<exists>j < size E. v \<in> E!j \<and> i < j) \<and> n< k}\<union>
            {(Cover n, Edge v e 0)| v e n i. i<length E \<and> e = E!i\<and> v \<in> e \<and> 
              \<not> (\<exists>j < size E. v \<in> E!j \<and> j < i) \<and> n < k},
          tail = fst, head = snd \<rparr>" 
  using in_vc vertex_cover_list_def G_def apply(auto simp add: vc_hc_def) 
  using in_vc_k_smaller by blast+ 

lemma is_wf_digraph:
  shows "wf_digraph G"
  by(auto simp add: G_def_2 wf_digraph_def) 

lemma function_of_edge_nodes: 
  assumes "v \<in> set (construct_cycle_1 E (CS) n C)" "\<forall>k'. v \<noteq> Cover k'"
  shows "\<exists> x. v \<in> set (construct_cycle_add_edge_nodes E x C)"
  using assms apply(induction CS arbitrary: n)
  by(auto) 

lemma edge_0_with_many_prems:
  assumes "ugraph (insert a (set Ea))" "v \<in> set (let u = get_second (a - {x}) in if u \<in> C then [Edge x a 0, Edge x a 1] else [Edge x a 0, Edge u a 0, Edge u a 1, Edge x a 1])"
    "x \<in> a" "\<forall>e u. u \<in> e \<longrightarrow> v = Edge u e (Suc 0) \<longrightarrow> e \<noteq> a \<and> e \<notin> set Ea"
  shows "\<exists>e u. v = Edge u e 0 \<and> u \<in> e \<and> (e = a \<or> e \<in> set Ea)"
proof -
  have not_empty: "(a - {x}) \<noteq> {}" 
    using edge_contains_minus_one_not_empty assms 
    by (metis list.set_intros(1) list.simps(15))
  then obtain u where u_def: "u = get_second (a-{x})" by(auto)
  then have "u \<in> a" 
    using not_empty get_second_in_edge by fast
  then show ?thesis using u_def assms apply(auto)
    by (smt One_nat_def empty_set insert_iff set_ConsD singleton_iff)
qed


lemma no_Cover_in_edge_function: 
  assumes "v \<in> set (construct_cycle_add_edge_nodes E x C)" "ugraph (set E)"
  shows "(\<exists> e u. v = Edge u e 0 \<and> u \<in> e \<and> e \<in> set E) \<or> (\<exists> e u. v = Edge u e 1 \<and> u \<in> e \<and> e \<in> set E)"
using assms apply(induction E arbitrary: ) apply(auto split: if_split_asm simp add: ugraph_implies_smaller_set_ugraph) 
  by(auto simp add: edge_0_with_many_prems)


lemma aux1:
  assumes "i<length Cs +n" "0<length Cs"
  shows "Cover i \<in> set (construct_cycle_1 E Cs n (set Cs))"
  using assms apply(induction Cs arbitrary: n) apply(simp) apply(auto) using no_Cover_in_edge_function
  sorry

lemma aux2:
  assumes "e \<in> set E" "v \<in> e"
  shows "Edge v e 0 \<in> set (construct_cycle_1 E Cov 0 (set Cov))"
  sorry

lemma aux3:
  assumes "e \<in> set E" "v \<in> e"
  shows "Edge v e 1 \<in> set (construct_cycle_1 E Cov 0 (set Cov))"
  sorry

lemma cycle_contains_all_verts:
  assumes "card (verts G) > 1"
  shows "(\<forall>x\<in> verts G. x \<in> set Cycle)" 
  apply(auto simp add: G_def Cycle_def vc_hc_def) 
  using aux1 
      apply (simp add: Cov_def(3)) 
      apply (metis Cov_def(3) gr_implies_not_zero list.size(3) trans_less_add1)
  using aux2 apply(blast)
  using aux3 apply(simp)
  using in_vc vertex_cover_list_def apply blast
  using in_vc in_vc_k_smaller apply blast
  done


lemma length_cycle:
  assumes "card (verts G) > 1" 
  shows "1 < length Cycle" 
proof -
  obtain u v where "u\<in> verts G" "v \<in> verts G" "u \<noteq> v" using card_greater_1_contains_two_elements assms by blast
  then have "u\<in> set Cycle" "v\<in> set Cycle" using cycle_contains_all_verts assms by blast+ 
  then have "card (set Cycle) > 1" using \<open>u\<noteq>v\<close> contains_two_card_greater_1 by fastforce 
  then show ?thesis 
    by (metis \<open>u \<in> set Cycle\<close> card_length leD length_pos_if_in_set less_numeral_extra(3) less_one linorder_neqE_nat)
qed 


lemma only_small_Cover_nodes_in_Cycle:
  assumes "length Cs +n \<le> k'" "0<k'"
  shows "Cover k' \<notin> set (construct_cycle_1 E (Cs) n C)"
  using assms 
  apply(induction Cs arbitrary: n) 
   apply(auto) 
  using no_Cover_in_edge_function in_vc vertex_cover_list_def by(blast) 

lemma function_of_cover_nodes:
  assumes "k\<le>k'" "0<k"
  shows "Cover k' \<notin> set (construct_cycle_1 E (Cov) 0 C)"
  using Cov_def assms by(auto simp add: only_small_Cover_nodes_in_Cycle) 
  

lemma nodes_of_cycle:
  assumes "v\<in> set Cycle" "k>0"
  shows "(\<exists>k'. v = Cover k' \<and> k' <k) \<or> (\<exists>e u. v = Edge u e 0 \<and> e \<in> set E \<and> u \<in> e) \<or> (\<exists>e u. v = Edge u e 1\<and> e \<in> set E \<and> u \<in> e)"
  using assms no_Cover_in_edge_function Cycle_def function_of_edge_nodes function_of_cover_nodes in_vc vertex_cover_list_def 
  by (metis (no_types, lifting) case_prodD le_eq_less_or_eq linorder_neqE_nat mem_Collect_eq)

lemma Cover_in_G:
  assumes "k' < k" "v = Cover k'"
  shows "v \<in> verts G"
  using G_def_2 assms by(auto)

lemma Edge0_in_G:
  assumes "e \<in> set E" "u\<in> e" "v = Edge u e 0"
  shows "v \<in> verts G"
  using G_def_2 assms by(auto)

lemma Edge1_in_G:
  assumes "e \<in> set E" "u \<in> e" "v = Edge u e 1"
  shows "v \<in> verts G"
  using G_def_2 assms by auto


lemma in_cycle_in_verts: 
  assumes "v \<in> set Cycle" "k>0"
  shows "v\<in> verts G" 
  using assms nodes_of_cycle Edge0_in_G Edge1_in_G Cover_in_G by blast


lemma 
  assumes "card S > 0"
  shows "\<exists>v. v\<in> S"
proof -
  have "S \<noteq> {}"
    using assms by(auto)
  then have "\<exists>v. v \<in> S" by(auto)
  then show ?thesis by auto
qed

lemma many_verts_impl_k_greater_0:
  assumes "card (verts G) > 1"
  shows "k>0"
proof (rule ccontr)
  assume "\<not> 0 < k" 
  then have "0 = k" by(auto)
  then have "Cov = []" using Cov_def by(auto)
  then have "Cycle = [(Cover 0)]" using Cycle_def by(auto)
  then have "set Cycle = {(Cover 0)}" by auto
  then have "verts G = {(Cover 0)}" using cycle_contains_all_verts assms apply(auto) 
    using card_greater_1_contains_two_elements by fastforce
  then show False using assms by(auto)
qed

lemma head_cycle_in_verts: 
  assumes "v = (hd Cycle)" "card (verts G) > 1" "Cycle \<noteq> []"
  shows "v \<in> (verts G)" 
  using in_cycle_in_verts assms many_verts_impl_k_greater_0 by(auto) 

lemma cycle_arcs_not_empty: 
  assumes "1 < size Cycle" 
  shows "vwalk_arcs Cycle \<noteq> []"
proof - (*Faster than sledgehammer generated*)
    obtain x y cs where "Cycle = x#y#cs" using assms 
      by (metis One_nat_def length_0_conv length_Cons less_numeral_extra(4) not_one_less_zero vwalk_arcs.cases)
    then have "vwalk_arcs Cycle = (x,y)#(vwalk_arcs (y#cs))" by simp
    then have "vwalk_arcs Cycle \<noteq> []" by auto
    then show ?thesis .
  qed

lemma is_cylce: 
  assumes "card (verts G) > 1" "v \<in> (verts G)" "v =(hd Cycle)" 
  shows "pre_digraph.cycle G (vwalk_arcs Cycle)"
proof -
  have "1 < size Cycle" using assms length_cycle by auto
  then have not_empty: "vwalk_arcs Cycle \<noteq> []" 
    using assms cycle_arcs_not_empty by auto
  have distinct: "distinct (tl (pre_digraph.awalk_verts G v (vwalk_arcs Cycle)))"sorry
  have contained: "set (vwalk_arcs Cycle) \<subseteq> arcs G" sorry
  have awalk: "pre_digraph.awalk G v (vwalk_arcs Cycle) v" sorry
  show ?thesis using not_empty distinct contained awalk pre_digraph.cycle_def pre_digraph.awalk_def by(auto)  
qed

lemma is_hc_cycle_graph: 
  shows "is_hc G Cycle"
  using cycle_contains_all_verts is_cylce is_hc_def head_cycle_in_verts 
  by fastforce


lemma vc_impl_hc_context: "vc_hc (E,k) \<in> hc"
  using is_wf_digraph is_hc_cycle_graph G_def hc_def
  by auto

end


subsection\<open>vc_hc (E, k) f \<in> hc  \<Longrightarrow> (E,k) \<in> VC\<close>
context 
  fixes E k  assumes "vc_hc (E, k) \<in> hc"
begin

end

subsection\<open> Main theorem \<close>

lemma vc_impl_hc: "(E,k) \<in> vertex_cover_list \<Longrightarrow> vc_hc (E,k) \<in> hc"
proof -
  assume in_vc: "(E,k)\<in> vertex_cover_list"
  then obtain Cov where "is_vertex_cover_list E Cov" "distinct Cov" "size Cov = k" 
    using vertex_cover_list_def 
    by (smt case_prodD mem_Collect_eq)
  then show ?thesis 
  using vc_impl_hc_context in_vc by blast
qed

lemma hc_impl_vc: "vc_hc (E,k) \<in> hc \<Longrightarrow> (E,k) \<in> vertex_cover_list"
proof -
  show ?thesis sorry
qed



theorem is_reduction_vc_to_hc:
  "is_reduction vc_hc vertex_cover_list hc"
  unfolding is_reduction_def using vc_impl_hc hc_impl_vc by(auto)


subsection\<open>Need to prove equivalence of Vertex-Cover\<close>

lemma is_vc_list_equal: 
  assumes "distinct E" "distinct V" 
  shows "is_vertex_cover (set E) (set V)\<longleftrightarrow> is_vertex_cover_list E V"
  apply(auto) 
  sorry

lemma "(set E, k) \<in> vertex_cover \<longleftrightarrow> (E, k) \<in> vertex_cover_list"
  using vertex_cover_def vertex_cover_list_def is_vc_list_equal apply(auto)
  sorry



end

