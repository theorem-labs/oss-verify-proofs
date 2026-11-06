(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StoreOk SymExec AxSymExec3K.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__AxSymExec3BK () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.MemImageType."; "LinuxProcessSemantics.Riscv.Instr."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AxSymExec3BK.AX2BK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AxSymExec3BK.AX2BK.WithSegs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AxSymExec3K.AX2K."; "Stdlib.Lists.List."; "Stdlib.PArith.BinPos.Pos."; "Stdlib.ZArith.BinInt.Z."], [["1None"; "1S"; "1Some"; "1app"; "1bool"; "1cons"; "1false"; "1fst"; "1list"; "1nat"; "1nil"; "1option"; "1orb"; "1pair"; "1prod"; "1reflect"]; ["1snd"; "1true"; "1tt"; "1unit"; "2and"; "2eq"; "2ex"; "2not"; "2or"; "3Forall"; "3map"; "4Z"; "4positive"; "0D"; "0K"; "5Segment"]; ["6aluop"; "6awidth"; "6branch_cond"; "6instr"; "6mulop"; "0P"; "0Q"; "7BI"; "7EINF"; "7FM"; "7NTI"; "7PKeep"; "7SPRo"; "7SX_OK"; "8kentry_overlayB"; "8kentry_readableB"]; ["8kn_overlayB"; "8kn_readableB"; "8sym_execTXB"; "8sym_execTXBI"; "8sym_execTXBI_go"; "8sym_execTXB_go"; "8sym_stepXB"; "8sym_stepXBI"; "8x_dischargeableB"; "8x_filterB"; "8zf_coversB"; "7all_gt"; "7alookupE"; "7amo_alignedbB"; "7amo_newvalB"; "7and_high_splitB"]; ["7and_low_splitB"; "7base_rangeB"; "7bc_ffk"; "7bc_fk"; "7bc_fs"; "7bc_ri"; "7bctx"; "7binfo"; "7bkey"; "7carryB"; "7carryG"; "7carryK"; "7carryK0"; "7chainK2"; "7chainKF"; "7chainRo"]; ["7chain_slow"; "7coeffs_divkB"; "7conc_exprB"; "7conc_tryB"; "7concretizeB"; "7decide_branchB"; "7disj_sidesB"; "7disj_sidesB_br"; "7disj_sides_xB"; "7disj_sides_xB_br"; "7ealignB"; "7ei_bid"; "7ei_br"; "7ei_k"; "7ei_m"; "7einfo"]; ["7end_hiB"; "7entriesG"; "7entriesV"; "7enum_branchB"; "7erange0B"; "7erangeB"; "7erange_fB"; "7extK0B"; "7extKB"; "7ext_fits"; "7ext_has"; "7fact_nowrapB"; "7find_rangeI"; "7flat_scB"; "7foldKB"; "7g1"]; ["7g1cB"; "7gran"; "7gst"; "7gtab"; "7gval"; "7in_sidesB"; "7in_sidesB_br"; "7in_sides_xB"; "7in_sides_xB_br"; "7inb"; "7intern"; "7is_lit0"; "7kcutB"; "7kdescr"; "7kdisj_apartB"; "7kdisj_apart_xB"]; ["7kfill_cutB"; "7know_lookupA0B"; "7know_lookupA0I"; "7know_lookupAB"; "7know_lookupABI"; "7know_lookupB"; "7kunk_cutB"; "7kw"; "7kx_add"; "7kx_bucket"; "7kx_build"; "7kx_cand0"; "7kx_candf"; "7kx_gkey"; "7kx_merge"; "7kx_wide0"]; ["7kzero_cutB"; "7lin_apart0B"; "7lin_apartB"; "7lin_branchB"; "7lin_brangeB"; "7lin_ge0B"; "7lin_ge0_scaledB"; "7lin_lowbits_knB"; "7lin_nowrapB"; "7lin_nowrapRB"; "7lin_nowrap_lB"; "7lin_srangeB"; "7lin_testB"; "7lin_test_relB"; "7log_lookupB"; "7lowbitsB"]; ["7lsplit_divB"; "7mkAluK0B"; "7mkAluKB"; "7mkAluwK0B"; "7mkAluwKB"; "7mkAnd0B"; "7mkAndB"; "7mkAndKB"; "7mkMdKB"; "7mkOrB"; "7mkSltB"; "7mkSrlB"; "7mk_fl"; "7mk_gl"; "7mk_kix"; "7mk_ri"]; ["7mk_sprepB"; "7mk_stxs"; "7mkbc"; "7mkbc0"; "7narrow_in"; "7narrow_maskB"; "7nt_add"; "7nt_bucket"; "7nt_empty"; "7nt_info"; "7nt_next"; "7ntab"; "7okey_eqb"; "7or_disjointB"; "7p_br_cache_ok"; "7pk_res"]; ["7prune1pB"; "7prune1pcB"; "7prune1pcK"; "7prune_zfB"; "7prunepcB"; "7ranges_apartB"; "7ranges_apart_pB"; "7ranges_apart_pcB"; "7ranges_apart_xB"; "7scan_entries"; "7srl_expandB"; "7storeok_scB"; "7stores_part"; "7strip"; "7stx"; "7sub_itvB"]; ["7sub_itvB_br"; "7sub_itv_xB"; "7sub_itv_xB_br"; "7sum_fact_xB"; "7sum_factsB"; "7sx_a"; "7sx_bid"; "7sx_sp"; "7sx_v"; "7sx_w"; "7sym_readB"; "7sym_readBI"; "7sym_stepB"; "7sym_stepBI"; "7tagged"; "7to_saddrKB"]; ["7verdict"; "7wr_coveredB"; "7wr_coveredB_br"; "7xhiB"; "7xinside0B"; "7xinsideB"; "7xinsideB_br"; "7xinside_numB"; "7xinside_numB_br"; "7xloB"; "7xt_nowrapB"; "7zband32B"; "9ELit"; "9KImg"; "9PTLeaf"; "9RUnknown"]; ["9SOk"; "9a_base"; "9a_off"; "9aluop_eqb"; "9amo_alignedb"; "9amo_newval"; "9and_high_split"; "9and_low_split"; "9base_range"; "9br_lookup"; "9cap_rd"; "9carry"; "9coeffs_divk"; "9conc_expr"; "9conc_try"; "9concretize"]; ["9decide_branch"; "9disj_sides"; "9disj_sides_br"; "9disj_sides_x"; "9disj_sides_x_br"; "9ealign"; "9elen"; "9end_hi"; "9enum_branch"; "9erange"; "9erange0"; "9erange_f"; "9expr"; "9expr_eqb"; "9extK"; "9extK0"]; ["9fact_nowrap"; "9facts_of"; "9find_range"; "9flat_sc"; "9foldK"; "9in_sides"; "9in_sides_br"; "9in_sides_x"; "9in_sides_x_br"; "9is_factb"; "9itab"; "9kbase"; "9kcut"; "9kdisj_apart"; "9kdisj_apart_x"; "9kentry"]; ["9kentry_overlay"; "9kentry_readable"; "9kfill_cut"; "9kn_overlay"; "9kn_readable"; "9know_lookup"; "9know_lookupA"; "9know_lookupA0"; "9ktrim"; "9kunk_cut"; "9kword_cut"; "9kzero_cut"; "9lin_apart"; "9lin_apart0"; "9lin_branch"; "9lin_brange"]; ["9lin_ge0"; "9lin_ge0_scaled"; "9lin_lowbits_kn"; "9lin_nowrap"; "9lin_nowrapR"; "9lin_nowrap_l"; "9lin_range"; "9lin_srange"; "9lin_test"; "9lin_test_rel"; "9log_lookup"; "9lowbits"; "9lres"; "9lsplit_div"; "9mkAluK"; "9mkAluK0"]; ["9mkAluwK"; "9mkAluwK0"; "9mkAnd"; "9mkAnd0"; "9mkAndK"; "9mkMdK"; "9mkOr"; "9mkSlt"; "9mkSrl"; "9mk_sprep"; "9mulop_eqb"; "9narrow_mask"; "9or_disjoint"; "9prune1p"; "9prune1pc"; "9prune_zf"]; ["9prunep"; "9prunepc"; "9pt_set"; "9ptree"; "9rangerel"; "9ranges_apart"; "9ranges_apart_p"; "9ranges_apart_pc"; "9ranges_apart_x"; "9rel_lit"; "9s_know"; "9saddr"; "9scripts"; "9sentry"; "9sfact"; "9sidecond"]; ["9sp_rng"; "9sprep"; "9srl_expand"; "9stepres"; "9storeok_sc"; "9sub_itv"; "9sub_itv_br"; "9sub_itv_x"; "9sub_itv_x_br"; "9sum_fact_x"; "9sum_facts"; "9sym_execTX"; "9sym_execTX_go"; "9sym_read"; "9sym_state"; "9sym_step"]; ["9sym_stepX"; "9to_saddrK"; "9wr_covered"; "9wr_covered_br"; "9x_dischargeable"; "9x_filter"; "9xhi"; "9xinside"; "9xinside0"; "9xinside_br"; "9xinside_num"; "9xinside_num_br"; "9xlo"; "9xt_nowrap"; "9xterms"; "9zband32"]; ["9zf_covers"; "9zlit64"; ":Forall2"; ":In"; ":filter"; ":flat_map"; ":rev"; ";eqb"; ";lt"; ";succ"; "<add"; "<div"; "<le"; "<lt"; "<of_nat"; "0a"]; ["0acc"; "0allkn"; "0aop"; "0apart"; "0b"; "0b1"; "0b2"; "0bc"; "0bi"; "0bid"; "0bk"; "0bnds"; "0br"; "0br1"; "0br2"; "0c"]; ["0cache"; "0cands"; "0ck"; "0d"; "0diffbase"; "0dts"; "0e"; "0ei"; "0first"; "0fk"; "0fs"; "0fuel"; "0g"; "0g'"; "0gr"; "0gs"]; ["0gs'"; "0h1"; "0hi"; "0hi1"; "0hi2"; "0hints"; "0i"; "0id"; "0id1"; "0id2"; "0imm"; "0infos"; "0j"; "0k"; "0k'"; "0k1"]; ["0k2"; "0kb"; "0kk"; "0kl"; "0kn"; "0kn0"; "0l"; "0l0"; "0l1"; "0l2"; "0len"; "0lo"; "0lo1"; "0lo2"; "0log"; "0m"]; ["0mk"; "0n"; "0n1"; "0n2"; "0neg"; "0oi"; "0okb"; "0old"; "0om"; "0op"; "0p"; "0pos"; "0r"; "0r1"; "0r2"; "0rb"]; ["0rest"; "0rk"; "0rn"; "0rts"; "0s"; "0same"; "0same_of"; "0sc"; "0scr"; "0scr'"; "0scs"; "0segs"; "0sp"; "0src"; "0ss"; "0ss'"]; ["0stops"; "0sx"; "0sx'"; "0sxo"; "0sxs"; "0t"; "0t'"; "0t1"; "0test"; "0ts"; "0v"; "0w"; "0w'"; "0w0"; "0wa"; "0wb"]; ["0wd"; "0wf"; "0wk"; "0wn"; "0wv"; "0x"; "0x0"; "0y"; "0z"]]).
Module AX2BK.
Import AX2K.
Create HintDb bceq discriminated.
Lemma p_aluop_eqb_eq : ltac2:(TCodec.tc2 tcn__AxSymExec3BK ">'Q0'E'4&WCr2r1%3221(A%73621r3%93:16p031pi:<1pi0=1").
Proof. intros [] []; cbn; intros; try reflexivity; discriminate. Qed.
Lemma p_mulop_eqb_eq : ltac2:(TCodec.tc2 tcn__AxSymExec3BK ">'Q4'E'4&Z:r2r1%3221(A%73621r3%93:16p031pi:<1pi0=1").
Proof. intros [] []; cbn; intros; try reflexivity; discriminate. Qed.
Lemma p_expr_eqb_eq : ltac2:(TCodec.tc2 tcn__AxSymExec3BK ">'X<'E'4&X=r2r1%3221(A%73621r3%93:16p031pQP@<1pQP<=1").
Proof.
induction x; destruct y; cbn; intros H; try discriminate;
repeat match goal with
| H : (_ && _)%bool = true |- _ => apply andb_prop in H; destruct H
end;
repeat match goal with
| H : Z.eqb _ _ = true |- _ => apply Z.eqb_eq in H
| H : Nat.eqb _ _ = true |- _ => apply Nat.eqb_eq in H
| H : Bool.eqb _ _ = true |- _ => apply Bool.eqb_prop in H
| H : aluop_eqb _ _ = true |- _ => apply p_aluop_eqb_eq in H
| H : mulop_eqb _ _ = true |- _ => apply p_mulop_eqb_eq in H
| H : expr_eqb ?a _ = true, IH : forall y, expr_eqb ?a y = true -> _ |- _ => apply IH in H
end; subst; reflexivity.
Qed.
Fixpoint first_var (e : expr) : option nat :=
match e with
| ELit _ => None
| EVar n => Some n
| EAlu _ a b | EAluw _ a b | EMd _ a b | EMdw _ a b =>
match first_var a with Some n => Some n | None => first_var b end
| EExt _ _ _ a => first_var a
| EBlob _ _ _ _ => None
end.
Definition vkey_of (e : expr) : option nat := first_var (fst (lit_strip e)).
Fixpoint lset {A : Type} (l : list (list A)) (n : nat) (x : A) {struct n} : list (list A) :=
match n, l with
| O, [] => [[x]]
| O, b :: rest => (x :: b) :: rest
| S m, [] => [] :: lset [] m x
| S m, b :: rest => b :: lset rest m x
end.
Definition lget {A : Type} (l : list (list A)) (n : nat) : list A := nth n l [].
Lemma lget_lset : forall (A : Type) (l : list (list A)) n x m,
lget (lset l n x) m = if Nat.eqb m n then x :: lget l m else lget l m.
Proof.
intros A l n. revert l. unfold lget. induction n as [|n IH]; intros l x m; destruct l as [|b rest]; destruct m as [|m]; cbn [lset nth Nat.eqb]; try reflexivity.
- destruct m; reflexivity.
- rewrite IH. destruct (Nat.eqb m n); destruct m; reflexivity.
- apply IH.
Qed.
Record rindex := RI { ri_vars : list (list kentry); ri_other : list kentry }.
Definition ri_bucket (ri : rindex) (k : option nat) : list kentry :=
match k with Some n => lget (ri_vars ri) n | None => ri_other ri end.
Fixpoint mk_ri (fk : list kentry) : rindex :=
match fk with
| [] => RI [] []
| K :: rest =>
let t := mk_ri rest in
match K with
| KRange e' _ _ =>
match vkey_of e' with
| Some n => RI (lset (ri_vars t) n K) (ri_other t)
| None => RI (ri_vars t) (K :: ri_other t)
end
| _ => t
end
end.
Definition find_rangeI (ri : rindex) (e : expr) : option (Z * Z) := find_range (ri_bucket ri (vkey_of e)) e.
Definition okey_eqb (a b : option nat) : bool :=
match a, b with Some x, Some y => Nat.eqb x y | None, None => true | _, _ => false end.
Lemma okey_eqb_spec : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "=';'9%211'?'Er2r1%33521&UL%1243%7231pi:91pi0:1").
Proof.
intros [x|] [y|]; cbn; try (constructor; congruence).
destruct (Nat.eqb_spec x y); constructor; congruence.
Qed.
Lemma ri_bucket_cons : forall t K e' lo hi k,
K = KRange e' lo hi ->
ri_bucket (match vkey_of e' with
| Some n => RI (lset (ri_vars t) n K) (ri_other t)
| None => RI (ri_vars t) (K :: ri_other t)
end) k
= if okey_eqb k (vkey_of e') then K :: ri_bucket t k else ri_bucket t k.
Proof.
intros t K e' lo hi k ->. destruct (vkey_of e') as [n|] eqn:Ev; destruct k as [m|]; cbn [ri_bucket ri_vars ri_other okey_eqb]; try reflexivity.
apply lget_lset.
Qed.
Lemma find_rangeI_eq : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "E'8'XO%211'X<'E';'>'K%2211%411&S<&U?r2%211r1%5221&XB%1253%>3931pj>@1pjDB1").
Proof.
intros fk e. unfold find_rangeI. induction fk as [|K rest IH].
- cbn [mk_ri]. destruct (vkey_of e) as [n|]; cbn; [unfold lget; destruct n; reflexivity | reflexivity].
- cbn [mk_ri]. destruct K as [a w v|a l|a l bk|lo hi|e1 m|e' lo hi|a n|a1 n1 a2 n2|a l c|a l];
cbn [find_range]; rewrite <- ?IH; try reflexivity.
rewrite (ri_bucket_cons (mk_ri rest) _ e' lo hi _ eq_refl).
destruct (okey_eqb_spec (vkey_of e) (vkey_of e')) as [EQ|NE].
+ cbn [find_range]. rewrite IH. reflexivity.
+ rewrite IH. destruct (expr_eqb e e') eqn:Ee.
* exfalso. apply NE. apply p_expr_eqb_eq in Ee. subst. reflexivity.
* destruct (lit_strip e) as [v c] eqn:Lx. destruct (lit_strip e') as [v' c'] eqn:Le'.
destruct (expr_eqb v v') eqn:Ev.
-- exfalso. apply NE. unfold vkey_of. rewrite Lx, Le'. cbn [fst]. apply p_expr_eqb_eq in Ev. subst. reflexivity.
-- destruct e; reflexivity.
Qed.
Record bctx : Type := BC {
bc_fk : list kentry;
bc_ffk : list kentry;
bc_fs : list sfact;
bc_ri : rindex
}.
Definition mkbc0 (fk : list kentry) (fs : list sfact) : bctx :=
BC fk (facts_of fk) fs (mk_ri (facts_of fk)).
Lemma lin_range_ext : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "M'X<';'>'K%2211%411pQP<61'8%6258%211'Er5r1%211r4%113%63;31pi0A1&YFr3r2%33:21%43832%=3B21p071poD@1pj0G1pmNE1pmLF1").
Proof. intros r1 r2 c ts H. induction ts as [|[k a] rest IH]; [reflexivity|]. cbn [lin_range]. rewrite H, IH. reflexivity. Qed.
Ltac beq_crush rw :=
repeat (first [ reflexivity
| progress rw
| lazymatch goal with
| |- ?L = _ =>
lazymatch L with
| (if ?c then _ else _) => destruct c
| (match ?x with _ => _ end) => destruct x
end
end ]).
Fixpoint erange_fB (fuel : nat) (bc : bctx) (e : expr) {struct fuel} : option (Z * Z) :=
match fuel with
| O => None
| S fuel' =>
let erange := erange_fB fuel' in
match find_rangeI (bc_ri bc) e with
| Some r => Some (clampi r)
| None =>
match (let l := lin_of e in
if lin_trivial l then None
else match lin_range (erange bc) (fst l) (snd l) with
| Some (lo, hi) =>
let q := zdiv64 lo in
if Z.eqb q (zdiv64 hi) then Some ((lo - q * two64)%Z, (hi - q * two64)%Z) else None
| None => None
end) with
| Some r => Some r
| None =>
match e with
| ELit z => let v := zmod64 z in Some (v, v)
| EVar _ => None
| EAlu op a b =>
match op with
| ALU_ADD =>
match erange bc a, erange bc b with
| Some (al, ah), Some (bl, bh) =>
if Z.ltb (ah + bh) two64 then Some ((al + bl)%Z, (ah + bh)%Z)
else if Z.leb two64 (al + bl) then Some ((al + bl - two64)%Z, (ah + bh - two64)%Z)
else None
| _, _ => None
end
| ALU_SUB =>
match erange bc a, erange bc b with
| Some (al, ah), Some (bl, bh) =>
if Z.leb bh al then Some ((al - bh)%Z, (ah - bl)%Z)
else if Z.ltb ah bl then Some ((al - bh + two64)%Z, (ah - bl + two64)%Z)
else None
| _, _ => None
end
| ALU_AND =>
match (match b, erange bc a with
| ELit m, Some (al, ah) =>
let m' := (m mod two64)%Z in
let j := Z.log2 (m' + 1) in
if (Z.eqb (m' + 1) (2 ^ j) && Z.leb (al / 2 ^ j) (ah / 2 ^ j) && Z.eqb (al / 2 ^ j) (ah / 2 ^ j))%bool
then Some ((al mod 2 ^ j)%Z, (ah mod 2 ^ j)%Z)
else let jh := Z.log2 (two64 - m') in
if (Z.eqb (two64 - m') (2 ^ jh) && Z.ltb jh 64)%bool
then Some ((al - al mod 2 ^ jh)%Z, (ah - ah mod 2 ^ jh)%Z)
else None
| _, _ => None
end) with
| Some r => Some r
| None =>
match erange bc a, erange bc b with
| Some (_, ah), Some (_, bh) => Some (0%Z, Z.min ah bh)
| Some (_, ah), None => Some (0%Z, ah)
| None, Some (_, bh) => Some (0%Z, bh)
| None, None => None
end
end
| ALU_OR =>
match erange bc a, erange bc b with
| Some (al, ah), Some (bl, bh) => Some (Z.max al bl, mask_cover (Z.max ah bh))
| _, _ => None
end
| ALU_XOR =>
match erange bc a, erange bc b with
| Some (_, ah), Some (_, bh) => Some (0%Z, mask_cover (Z.max ah bh))
| _, _ => None
end
| ALU_SRL =>
match erange bc a, lit_shamt b with
| Some (al, ah), Some s => Some ((al / 2 ^ s)%Z, (ah / 2 ^ s)%Z)
| _, _ => None
end
| ALU_SRA =>
match erange bc a, lit_shamt b with
| Some (al, ah), Some s =>
if Z.ltb ah (2 ^ 63) then Some ((al / 2 ^ s)%Z, (ah / 2 ^ s)%Z) else None
| _, _ => None
end
| ALU_SLL =>
match erange bc a, lit_shamt b with
| Some (al, ah), Some s =>
if Z.ltb (ah * 2 ^ s) two64 then Some ((al * 2 ^ s)%Z, (ah * 2 ^ s)%Z) else None
| _, _ => None
end
| ALU_SLTU =>
match erange bc a, erange bc b with
| Some (al, ah), Some (bl, bh) =>
if Z.ltb ah bl then Some (1%Z, 1%Z)
else if Z.leb bh al then Some (0%Z, 0%Z) else Some (0%Z, 1%Z)
| _, _ => Some (0%Z, 1%Z)
end
| ALU_SLT =>
match erange bc a, erange bc b with
| Some (al, ah), Some (bl, bh) =>
if (Z.ltb ah (2 ^ 63) && Z.ltb bh (2 ^ 63))%bool then
(if Z.ltb ah bl then Some (1%Z, 1%Z)
else if Z.leb bh al then Some (0%Z, 0%Z) else Some (0%Z, 1%Z))
else Some (0%Z, 1%Z)
| _, _ => Some (0%Z, 1%Z)
end
end
| EAluw op a b =>
match op with
| ALU_ADD =>
match erange bc a, erange bc b with
| Some (al, ah), Some (bl, bh) =>
let bl' := if Z.eqb bl bh then zsigned64 bl else bl in
let bh' := if Z.eqb bl bh then zsigned64 bh else bh in
if (Z.leb 0 (al + bl') && Z.ltb (ah + bh') (2 ^ 31))%bool
then Some ((al + bl')%Z, (ah + bh')%Z) else None
| _, _ => None
end
| ALU_SUB =>
match erange bc a, erange bc b with
| Some (al, ah), Some (bl, bh) =>
if (Z.leb bh al && Z.ltb (ah - bl) (2 ^ 31))%bool
then Some ((al - bh)%Z, (ah - bl)%Z) else None
| _, _ => None
end
| ALU_SLL =>
match erange bc a, lit_shamt b with
| Some (al, ah), Some s =>
let s' := (s mod 32)%Z in
if Z.ltb (ah * 2 ^ s') (2 ^ 31) then Some ((al * 2 ^ s')%Z, (ah * 2 ^ s')%Z) else None
| _, _ => None
end
| ALU_SRL =>
match erange bc a, lit_shamt b with
| Some (al, ah), Some s =>
let s' := (s mod 32)%Z in
if (Z.ltb ah (2 ^ 32) && (Z.ltb 0 s' || Z.ltb ah (2 ^ 31)))%bool
then Some ((al / 2 ^ s')%Z, (ah / 2 ^ s')%Z) else None
| _, _ => None
end
| ALU_SRA =>
match erange bc a, lit_shamt b with
| Some (al, ah), Some s =>
let s' := (s mod 32)%Z in
if Z.ltb ah (2 ^ 31) then Some ((al / 2 ^ s')%Z, (ah / 2 ^ s')%Z) else None
| _, _ => None
end
| _ => None
end
| EMd op a b =>
match op with
| M_MUL =>
match erange bc a, erange bc b with
| Some (al, ah), Some (bl, bh) =>
if (Z.leb 0 al && Z.leb 0 bl && Z.ltb (ah * bh) two64)%bool
then Some ((al * bl)%Z, (ah * bh)%Z) else None
| _, _ => None
end
| M_MULHU =>
match erange bc a, erange bc b with
| Some (al, ah), Some (bl, bh) =>
if (Z.leb 0 al && Z.leb 0 bl)%bool
then Some ((al * bl / two64)%Z, (ah * bh / two64)%Z) else None
| _, _ => None
end
| M_DIVU =>
match erange bc a, b with
| Some (al, ah), ELit d =>
let d' := (d mod two64)%Z in
if Z.ltb 0 d' then Some ((al / d')%Z, (ah / d')%Z) else None
| _, _ => None
end
| M_REMU =>
match erange bc a, b with
| Some (al, ah), ELit d =>
let d' := (d mod two64)%Z in
if Z.ltb 0 d' then Some (0%Z, Z.min ah (d' - 1)) else None
| _, _ => None
end
| _ => None
end
| EMdw _ _ _ => None
| EExt sx lo n a =>
let w := (2 ^ (8 * Z.of_nat n))%Z in
if sx then
match lo, erange bc a with
| O, Some (al, ah) =>
if (Z.leb 0 al && Z.ltb ah (w / 2))%bool then Some (al, ah)
else if (Nat.leb 1 n && Nat.leb n 8 && Z.leb (w / 2) al && Z.ltb ah w)%bool
then Some ((two64 - w + al)%Z, (two64 - w + ah)%Z) else None
| _, _ => None
end
else
match lo, erange bc a with
| O, Some (al, ah) =>
if (Z.leb 0 al && Z.ltb ah w)%bool then Some (al, ah) else Some (0%Z, Z.min (w - 1) (two64 - 1))
| _, _ => Some (0%Z, Z.min (w - 1) (two64 - 1))
end
| EBlob sx k i n =>
if sx then Some (0%Z, two64m1) else Some (0%Z, Z.min (2 ^ (8 * Z.of_nat n) - 1) (two64 - 1))%Z
end
end
end
end.
Definition erange0B (bc : bctx) (e : expr) : option (Z * Z) := erange_fB erange_fuel bc e.
Definition erangeB (bc : bctx) (e : expr) : option (Z * Z) :=
let r := erange0B bc e in
let '(e', s) := deand e in
if Z.eqb s 0 then r else
let g := lin_galign (lin_of e) in
let rnd := fun p : Z * Z => Some (round_itv g (fst p) (snd p)) in
match erange0B bc (unlin (lin_of e')) with
| Some (lo', hi') =>
if Z.leb s lo' then
match r with
| Some (lo, hi) => rnd (Z.max lo (lo' - s), Z.min hi hi')
| None => rnd ((lo' - s)%Z, hi')
end
else match r with Some p => rnd p | None => None end
| None => match r with Some p => rnd p | None => None end
end.
Definition base_rangeB (bc : bctx) (e : expr) : option (Z * Z) :=
match e with ELit z => let v := (z mod two64)%Z in Some (v, v) | _ => erangeB bc e end.
Definition ealignB (bc : bctx) (e : expr) : Z := Z.max (ealign0 (bc_ffk bc) e) (pageup_align e).
Definition lin_nowrapB (bc : bctx) (e : expr) : bool :=
let l := lin_of e in
match lin_range (erangeB bc) (fst l) (snd l) with
| Some (lo, hi) => (Z.leb 0 lo && Z.ltb hi two64)%bool
| None => false
end.
Fixpoint srl_expandB (bc : bctx) (ts : list (Z * expr)) : Z * list (Z * expr) :=
match ts with
| [] => (0%Z, [])
| (k, a) :: rest =>
let '(c, ts') := srl_expandB bc rest in
let keep := (c, lins_e k a ts') in
match a with
| EAlu ALU_SRL e (ELit s) =>
let m := (2 ^ ((s mod two64) mod 64))%Z in
if (Z.eqb (k mod m)%Z 0%Z && lin_nowrapB bc e)%bool then
let q := (k / m)%Z in
let le := lin_of e in
if Z.leb ((s mod two64) mod 64) (ealignB bc e) then
((c + q * fst le)%Z, fold_right (fun t acc => lins_e (q * fst t)%Z (snd t) acc) ts' (snd le))
else
((c + q * fst le)%Z,
lins_e (- q)%Z (srl_rem e m) (fold_right (fun t acc => lins_e (q * fst t)%Z (snd t) acc) ts' (snd le)))
else keep
| EAlu ALU_AND e (ELit mk) =>
match highmask_s mk with
| Some s =>
if lin_nowrapB bc e then
let le := lin_of e in
((c + k * fst le)%Z,
lins_e (- k)%Z (srl_rem e (2 ^ s)) (fold_right (fun t acc => lins_e (k * fst t)%Z (snd t) acc) ts' (snd le)))
else keep
| None => keep
end
| _ => keep
end
end.
Definition fact_nowrapB (bc : bctx) (e : expr) (hi : Z) : bool :=
let l := lin_of e in
match lin_range (erangeB bc) (fst l) (snd l) with
| Some (a, b) => (Z.ltb b two64 && Z.ltb hi (a + two64))%bool
| None => false
end.
Definition sum_fact_xB (bc : bctx) (ts : list (Z * expr)) (lo hi : Z) : list sfact :=
let '(c2, ts2) := srl_expandB bc ts in
match ts2 with
| _ :: _ => if Z.eqb c2 0 then [] else [(ts2, ((lo - c2)%Z, (hi - c2)%Z))]
| [] => []
end.
Fixpoint sum_factsB (bc : bctx) (kn : list kentry) : list sfact :=
match kn with
| [] => []
| KRange e lo hi :: rest =>
match e with
| EVar _ => sum_factsB bc rest
| _ =>
match lin_of e with
| (c, (_ :: _ :: _) as ts) =>
if fact_nowrapB bc e hi then (ts, ((lo - c)%Z, (hi - c)%Z)) :: sum_fact_xB bc ts (lo - c)%Z (hi - c)%Z ++ sum_factsB bc rest
else sum_factsB bc rest
| _ => sum_factsB bc rest
end
end
| _ :: rest => sum_factsB bc rest
end.
Lemma bc_fk_mkbc0 : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "?'8'XO%211&ZN%411'E&R3&UCr2r1%3221%511%73:14pjF91pjD<1"). Proof. reflexivity. Qed.
Lemma bc_ffk_mkbc0 : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "A'8'XO%211&ZN%411'E&R2&UCr2r1%3221%511&XA%115%93<31pjF;1pjD>1"). Proof. reflexivity. Qed.
Lemma find_rangeI_mkbc0 : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "L'8'XO%211&ZN%411'E'X<';'>'K%2211%411pj>61&S<&R5&UCr2r1%3221%511%711&XB&XA%117%311%D3=51pjFF1pjDI1").
Proof. intros. apply functional_extensionality. intros e. apply find_rangeI_eq. Qed.
#[export] Hint Rewrite bc_fk_mkbc0 bc_ffk_mkbc0 find_rangeI_mkbc0 : bceq.
Ltac bcfe := repeat (apply functional_extensionality; intros ?).
Lemma erange_fB_eqf0 : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "M'8'XO%211&ZN%411'9'E'X<';'>'K%2211%411pj>61&S6r1&UCr3r2%3221%6251&X;&XA%116%3291%C3<51pjHE1pjFG1pjDJ1").
Proof.
intros fk fs fuel. induction fuel as [|f IH]; bcfe; [reflexivity|].
cbn [erange_fB erange_f]. rewrite IH. (repeat first [ rewrite find_rangeI_mkbc0 ]). reflexivity.
Qed.
#[export] Hint Rewrite erange_fB_eqf0 : bceq.
Lemma erange0B_eqf0 : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "H'8'XO%211&ZN%411'E'X<';'>'K%2211%411pj>61&S4&UCr2r1%3221%511&X:%115%@3931pjFB1pjDE1").
Proof. intros. bcfe. unfold erange0B, erange0. (repeat first [ rewrite erange_fB_eqf0 ]). reflexivity. Qed.
#[export] Hint Rewrite erange0B_eqf0 : bceq.
Lemma erangeB_eqf0 : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "H'8'XO%211&ZN%411'E'X<';'>'K%2211%411pj>61&S5&UCr2r1%3221%511&X9%115%@3931pjFB1pjDE1").
Proof. intros. bcfe. unfold erangeB, erange. (repeat first [ rewrite erange0B_eqf0 ]). reflexivity. Qed.
#[export] Hint Rewrite erangeB_eqf0 : bceq.
Lemma base_rangeB_eqf0 : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "H'8'XO%211&ZN%411'E'X<';'>'K%2211%411pj>61&R1&UCr2r1%3221%511&WH%115%@3931pjFB1pjDE1").
Proof. intros. bcfe. unfold base_rangeB, base_range. (repeat first [ rewrite erangeB_eqf0 ]). reflexivity. Qed.
#[export] Hint Rewrite base_rangeB_eqf0 : bceq.
Lemma ealignB_eqf0 : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "D'8'XO%211&ZN%411'E'X<'Kpj>21&RJ&UCr2r1%3221%511&X5%115%<3931pjF>1pjDA1").
Proof. intros. bcfe. unfold ealignB, ealign. (repeat first [ rewrite bc_ffk_mkbc0 ]). reflexivity. Qed.
#[export] Hint Rewrite ealignB_eqf0 : bceq.
Lemma lin_nowrapB_eqf0 : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "D'8'XO%211&ZN%411'E'X<'4pj>21&TH&UCr2r1%3221%511&YC%115%<3931pjF>1pjDA1").
Proof. intros. bcfe. unfold lin_nowrapB, lin_nowrap. (repeat first [ rewrite erangeB_eqf0 ]). reflexivity. Qed.
#[export] Hint Rewrite lin_nowrapB_eqf0 : bceq.
Lemma srl_expandB_eqf0 : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "H'8'XO%211&ZN%411'E'>'K'X<%3221%:11%5241poD21&V:&UCr2r1%3221%511&[2%115%@3931pjFB1pjDE1").
Proof.
intros fk fs. apply functional_extensionality; intros ts.
induction ts as [|[k a] rest IH]; intros; bcfe; [reflexivity|].
cbn [srl_expandB srl_expand]. rewrite IH. (repeat first [ rewrite ealignB_eqf0 | rewrite lin_nowrapB_eqf0 ]). reflexivity.
Qed.
#[export] Hint Rewrite srl_expandB_eqf0 : bceq.
Lemma fact_nowrapB_eqf0 : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "F'8'XO%211&ZN%411'E'X<'K'4pk621pj>41&S;&UCr2r1%3221%511&X@%115%>3931pjF@1pjDC1").
Proof. intros. bcfe. unfold fact_nowrapB, fact_nowrap. (repeat first [ rewrite erangeB_eqf0 ]). reflexivity. Qed.
#[export] Hint Rewrite fact_nowrapB_eqf0 : bceq.
Lemma sum_fact_xB_eqf0 : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "I'8'XO%211&ZN%411'E'>'K'X<%3221%:11pk647plH51poD31&VC&UCr2r1%3221%511&[9%115%A3931pjFC1pjDF1").
Proof. intros. bcfe. unfold sum_fact_xB, sum_fact_x. (repeat first [ rewrite srl_expandB_eqf0 ]). reflexivity. Qed.
#[export] Hint Rewrite sum_fact_xB_eqf0 : bceq.
Lemma sum_factsB_eqf0 : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "B'8'XO%211&ZN%411'Epl:42&VD&UCr2r1%3221%511&[:%115%:3931pjF<1pjD?1").
Proof.
intros fk fs. apply functional_extensionality; intros kn.
induction kn as [|K rest IH]; intros; bcfe; [reflexivity|].
cbn [sum_factsB sum_facts]. rewrite IH. (repeat first [ rewrite fact_nowrapB_eqf0 | rewrite sum_fact_xB_eqf0 ]). reflexivity.
Qed.
#[export] Hint Rewrite sum_factsB_eqf0 : bceq.
Definition mkbc (fk : list kentry) : bctx := mkbc0 fk (sum_factsB (mkbc0 fk []) fk).
Lemma bc_fk_mkbc : ltac2:(TCodec.tc2 tcn__AxSymExec3BK ";'8'XO%211'E&R3&UBr1%211%411%63713pjD81"). Proof. reflexivity. Qed.
Lemma bc_ffk_mkbc : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "='8'XO%211'E&R2&UBr1%211%411&XA%114%83931pjD:1"). Proof. reflexivity. Qed.
Lemma bc_fs_mkbc : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "?'8'XO%211'E&ZN%511&R4&UBr1%211%411&[:%1244%:3831pjD<1").
Proof. intros. unfold mkbc. cbn [bc_fs mkbc0]. rewrite sum_factsB_eqf0. reflexivity. Qed.
Lemma find_rangeI_mkbc : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "H'8'XO%211'E'X<';'>'K%2211%411pj>61&S<&R5&UBr1%211%411%611&XB&XA%116%311%C3<51pjDE1").
Proof. intros. unfold mkbc. apply find_rangeI_mkbc0. Qed.
#[export] Hint Rewrite bc_fk_mkbc bc_ffk_mkbc bc_fs_mkbc find_rangeI_mkbc : bceq.
Lemma erange_fB_eqf : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "I'8'XO%211'9'E'X<';'>'K%2211%411pj>61&S6r1&UBr2%211%5241&X;&XA%115%3281%B3;51pjHD1pjDF1").
Proof. intros. unfold mkbc. apply erange_fB_eqf0. Qed.
#[export] Hint Rewrite erange_fB_eqf : bceq.
Lemma erange0B_eqf : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "D'8'XO%211'E'X<';'>'K%2211%411pj>61&S4&UBr1%211%411&X:%114%?3831pjDA1").
Proof. intros. unfold mkbc. apply erange0B_eqf0. Qed.
#[export] Hint Rewrite erange0B_eqf : bceq.
Lemma erangeB_eqf : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "D'8'XO%211'E'X<';'>'K%2211%411pj>61&S5&UBr1%211%411&X9%114%?3831pjDA1").
Proof. intros. unfold mkbc. apply erangeB_eqf0. Qed.
#[export] Hint Rewrite erangeB_eqf : bceq.
Lemma base_rangeB_eqf : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "D'8'XO%211'E'X<';'>'K%2211%411pj>61&R1&UBr1%211%411&WH%114%?3831pjDA1").
Proof. intros. unfold mkbc. apply base_rangeB_eqf0. Qed.
#[export] Hint Rewrite base_rangeB_eqf : bceq.
Lemma ealignB_eqf : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "@'8'XO%211'E'X<'Kpj>21&RJ&UBr1%211%411&X5%114%;3831pjD=1").
Proof. intros. unfold mkbc. apply ealignB_eqf0. Qed.
#[export] Hint Rewrite ealignB_eqf : bceq.
Lemma lin_nowrapB_eqf : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "@'8'XO%211'E'X<'4pj>21&TH&UBr1%211%411&YC%114%;3831pjD=1").
Proof. intros. unfold mkbc. apply lin_nowrapB_eqf0. Qed.
#[export] Hint Rewrite lin_nowrapB_eqf : bceq.
Lemma srl_expandB_eqf : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "D'8'XO%211'E'>'K'X<%3221%811%5241poD21&V:&UBr1%211%411&[2%114%?3831pjDA1").
Proof. intros. unfold mkbc. apply srl_expandB_eqf0. Qed.
#[export] Hint Rewrite srl_expandB_eqf : bceq.
Lemma fact_nowrapB_eqf : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "B'8'XO%211'E'X<'K'4pk621pj>41&S;&UBr1%211%411&X@%114%=3831pjD?1").
Proof. intros. unfold mkbc. apply fact_nowrapB_eqf0. Qed.
#[export] Hint Rewrite fact_nowrapB_eqf : bceq.
Lemma sum_fact_xB_eqf : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "G'8'XO%211'E'>'K'X<%3221%811&ZN%:11pk661plH71poD51&VC&UBr1%211%411&[9%114%B3831pjDD1").
Proof. intros. unfold mkbc. apply sum_fact_xB_eqf0. Qed.
#[export] Hint Rewrite sum_fact_xB_eqf : bceq.
Lemma sum_factsB_eqf : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "@'8'XO%211'E&ZN%511pl:41&VD&UBr1%211%411&[:%114%;3831pjD=1").
Proof. intros. unfold mkbc. apply sum_factsB_eqf0. Qed.
#[export] Hint Rewrite sum_factsB_eqf : bceq.
Definition lin_test_relB (bc : bctx) (c : Z) (ts : list (Z * expr)) (test : Z -> Z -> bool) : bool :=
match bc_fs bc with
| [] => false
| fs =>
match sum_subst fs ts 0 0 false with
| (ts', (lo0, hi0), true) =>
match lin_range (erangeB bc) c ts' with
| Some (lo, hi) => test (lo + lo0)%Z (hi + hi0)%Z
| None => false
end
| _ => false
end
end.
Definition lin_testB (bc : bctx) (c : Z) (ts : list (Z * expr)) (test : Z -> Z -> bool) : bool :=
match lin_range (erangeB bc) c ts with
| Some (lo, hi) => if test lo hi then true else lin_test_relB bc c ts test
| None => lin_test_relB bc c ts test
end.
Definition lin_srangeB (bc : bctx) (e : expr) : option (Z * Z) :=
let l := lin_of e in
let j := srl_scale_need (snd l) in
if (if Z.leb 0 j then Z.leb j 24 else false) then
let sc := (2 ^ j)%Z in
let ts := List.map (fun t => ((sc * fst t)%Z, snd t)) (snd l) in
let '(c2, t2) := srl_expandB bc ts in
let '(c3, t3) := (if has_srl t2 then srl_expandB bc t2 else (0%Z, t2)) in
match lin_range (erangeB bc) (sc * fst l + c2 + c3)%Z t3 with
| Some (lo', hi') =>
let lo := zcdiv lo' sc in let hi := (hi' / sc)%Z in
if (if Z.leb 0 lo then (if Z.leb lo hi then Z.ltb hi two64 else false) else false) then Some (lo, hi) else None
| None => None
end
else None.
Definition lin_nowrapRB (bc : bctx) (e : expr) : bool :=
let l := lin_of e in
let '(c2, t2) := srl_expandB bc (snd l) in
if lin_testB bc (fst l + c2)%Z t2 (fun lo hi => (Z.leb 0 lo && Z.ltb hi two64)%bool) then true
else
match lin_srangeB bc e with Some _ => true | None => false end.
Definition lin_apart0B (bc : bctx) (b1 : expr) (k1 n1 : Z) (b2 : expr) (k2 n2 : Z) : bool :=
(lin_nowrapRB bc b1 && lin_nowrapRB bc b2 &&
let l1 := lin_of b1 in let l2 := lin_of b2 in
lin_testB bc (fst l2 + k2 - fst l1 - k1)%Z (lsub_e (snd l2) (snd l1))
(fun lo hi => (Z.leb n1 lo || Z.leb hi (- n2))%bool))%bool.
Definition lin_apartB (bc : bctx) (b1 : expr) (k1 n1 : Z) (b2 : expr) (k2 n2 : Z) : bool :=
if shares_var b1 b2 then lin_apart0B bc b1 k1 n1 b2 k2 n2 else false.
Definition lin_brangeB (bc : bctx) (e : expr) : option (Z * Z) :=
let l := lin_of e in
match bc_fs bc with
| [] => None
| fs =>
match sum_subst fs (snd l) 0 0 false with
| (ts', (lo0, hi0), true) =>
match lin_range (erangeB bc) (fst l) ts' with
| Some (lo, hi) =>
let lo' := (lo + lo0)%Z in let hi' := (hi + hi0)%Z in
if (Z.leb 0 lo' && Z.ltb hi' two64)%bool then Some (lo', hi') else None
| None => None
end
| _ => None
end
end.
Definition xloB (bc : bctx) (e : expr) : option Z :=
match e with
| ELit z => Some (zlit64 z)
| _ => match erangeB bc e with
| Some (lo, _) => Some lo
| None => match lin_brangeB bc e with
| Some (lo, _) => Some lo
| None => match lin_srangeB bc e with Some (lo, _) => Some lo | None => None end
end
end
end.
Definition xhiB (bc : bctx) (e : expr) : option Z :=
match e with
| ELit z => Some (zlit64 z)
| _ => match erangeB bc e with
| Some (_, hi) => Some hi
| None => match lin_brangeB bc e with
| Some (_, hi) => Some hi
| None => match lin_srangeB bc e with Some (_, hi) => Some hi | None => None end
end
end
end.
Fixpoint xt_nowrapB (bc : bctx) (ts : xterms) : bool :=
match ts with [] => true | (e, _) :: r => lin_nowrapRB bc e && xt_nowrapB bc r end.
Definition lin_ge0_scaledB (bc : bctx) (c : Z) (ts : list (Z * expr)) : bool :=
let j := srl_scale_need ts in
if (if Z.ltb 0 j then Z.leb j 24 else false) then
let sc := (2 ^ j)%Z in
let ts' := List.map (fun t => ((sc * fst t)%Z, snd t)) ts in
let '(c2, t2) := srl_expandB bc ts' in
let '(c3, t3) := (if has_srl t2 then srl_expandB bc t2 else (0%Z, t2)) in
lin_testB bc (sc * c + c2 + c3)%Z t3 (fun lo _ => Z.leb 0 lo)
else false.
Definition lin_ge0B (bc : bctx) (pos neg : xterms) : bool :=
let al := ealignB bc in
(xt_nowrapB bc pos && xt_nowrapB bc neg &&
(let c1 := (xt_const pos - xt_const neg)%Z in let t1 := lsub_e (xt_lin pos) (xt_lin neg) in
if lin_testB bc c1 t1 (slack_test al c1 t1) then true
else let '(c2, t2) := srl_expandB bc t1 in
if lin_testB bc (c1 + c2)%Z t2 (slack_test2 al c1 t1 (c1 + c2)%Z t2) then true
else
if (if has_srl t2 then
let '(c3, t3) := srl_expandB bc t2 in
lin_testB bc (c1 + c2 + c3)%Z t3 (slack_test2 al c1 t1 (c1 + c2 + c3)%Z t3)
else false) then true
else
lin_ge0_scaledB bc c1 t1))%bool.
Definition xinside0B (bc : bctx) (b1 : expr) (k1 : Z) (n1 : expr) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
if lin_ge0B bc [(b1, k1)] [(b2, k2)] then lin_ge0B bc [(b2, k2); (n2, 0%Z)] [(b1, k1); (n1, 0%Z)] else false.
Definition xinside_numB (bc : bctx) (b1 : expr) (k1 : Z) (n1 : expr) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
match xloB bc b2, xhiB bc b2 with
| Some lo2, Some hi2 =>
if Z.eqb lo2 hi2 then
match base_rangeB bc b1, xhiB bc n1, xloB bc n2 with
| Some (lo1, hi1), Some h1, Some l2 => Z.leb (lo2 + k2) (lo1 + k1) && Z.leb (hi1 + k1 + h1) (lo2 + k2 + l2)
| _, _, _ => false
end
else false
| _, _ => false
end.
Definition xinsideB (bc : bctx) (b1 : expr) (k1 : Z) (n1 : expr) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
if shares_var b1 b2 then xinside0B bc b1 k1 n1 b2 k2 n2
else if novars b2 then
(if xinside_numB bc b1 k1 n1 b2 k2 n2 then true
else match n1 with ELit _ => false | _ => xinside0B bc b1 k1 n1 b2 k2 n2 end)
else false.
Definition sub_itvB (bc : bctx) (b : expr) (k n : Z) (c : saddr) (m : expr) : bool :=
if (if (expr_eqb b (a_base c) && Z.leb (a_off c) k)%bool then
match xloB bc m with Some ml => Z.leb (k + n) (a_off c + ml) | None => false end
else false)
then true
else
if (Z.leb 0 n && Z.ltb n two64)%bool then xinsideB bc b k (ELit n) (a_base c) (a_off c) m else false.
Fixpoint kdisj_apartB (bc : bctx) (kn : list kentry) (b1 : expr) (k1 n1 : Z) (b2 : expr) (k2 n2 : Z) : bool :=
match kn with
| [] => false
| KDisj c1 m1 c2 m2 :: rest =>
if (if sub_itvB bc b1 k1 n1 c1 m1 then sub_itvB bc b2 k2 n2 c2 m2 else false) then true
else if (if sub_itvB bc b1 k1 n1 c2 m2 then sub_itvB bc b2 k2 n2 c1 m1 else false) then true
else kdisj_apartB bc rest b1 k1 n1 b2 k2 n2
| _ :: rest => kdisj_apartB bc rest b1 k1 n1 b2 k2 n2
end.
Definition ranges_apartB (bc : bctx) (b1 : expr) (k1 n1 : Z) (b2 : expr) (k2 n2 : Z) : bool :=
if expr_eqb b2 b1 then (Z.leb (k1 + n1) k2 || Z.leb (k2 + n2) k1)%bool else
if (match base_rangeB bc b1, base_rangeB bc b2 with
| Some (lo1, hi1), Some (lo2, hi2) =>
(Z.leb (hi1 + k1 + n1) (lo2 + k2) || Z.leb (hi2 + k2 + n2) (lo1 + k1))%bool
| _, _ => false
end) then true
else if kdisj_apartB bc (bc_fk bc) b1 k1 n1 b2 k2 n2 then true
else lin_apartB bc b1 k1 n1 b2 k2 n2.
Definition sub_itv_xB (bc : bctx) (b : expr) (k : Z) (n : expr) (c : saddr) (m : expr) : bool :=
xinsideB bc b k n (a_base c) (a_off c) m.
Fixpoint kdisj_apart_xB (bc : bctx) (kn : list kentry) (b1 : expr) (k1 : Z) (n1 : expr) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
match kn with
| [] => false
| KDisj c1 m1 c2 m2 :: rest =>
if (if sub_itv_xB bc b1 k1 n1 c1 m1 then sub_itv_xB bc b2 k2 n2 c2 m2 else false) then true
else if (if sub_itv_xB bc b1 k1 n1 c2 m2 then sub_itv_xB bc b2 k2 n2 c1 m1 else false) then true
else kdisj_apart_xB bc rest b1 k1 n1 b2 k2 n2
| _ :: rest => kdisj_apart_xB bc rest b1 k1 n1 b2 k2 n2
end.
Definition end_hiB (bc : bctx) (b : expr) (k : Z) (n : expr) (lo1 hi1 h1 : Z) : option Z :=
match n with
| ELit _ => None
| _ => if (if Z.leb 0 (lo1 + k) then Z.ltb (hi1 + k + h1) two64 else false)
then match find_rangeI (bc_ri bc) (mkAlu ALU_ADD (mkAlu ALU_ADD b (ELit k)) n) with
| Some (_, ehi) => Some ehi
| None => None
end
else None
end.
Definition ranges_apart_xB (bc : bctx) (b1 : expr) (k1 : Z) (n1 : expr) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
match n1, n2 with
| ELit z1, ELit z2 => ranges_apartB bc b1 k1 (zlit64 z1) b2 k2 (zlit64 z2)
| _, _ =>
if (match base_rangeB bc b1, base_rangeB bc b2, xhiB bc n1, xhiB bc n2 with
| Some (lo1, hi1), Some (lo2, hi2), Some h1, Some h2 =>
if (Z.leb (hi1 + k1 + h1) (lo2 + k2) || Z.leb (hi2 + k2 + h2) (lo1 + k1))%bool then true
else
if match end_hiB bc b1 k1 n1 lo1 hi1 h1 with Some e1 => Z.leb e1 (lo2 + k2) | None => false end then true
else match end_hiB bc b2 k2 n2 lo2 hi2 h2 with Some e2 => Z.leb e2 (lo1 + k1) | None => false end
| _, _, _, _ => false
end) then true
else if kdisj_apart_xB bc (bc_fk bc) b1 k1 n1 b2 k2 n2 then true
else if negb (shares_var b1 b2) then false
else if lin_ge0B bc [(b2, k2)] [(b1, k1); (n1, 0%Z)] then true
else lin_ge0B bc [(b1, k1)] [(b2, k2); (n2, 0%Z)]
end.
Fixpoint disj_sidesB (bc : bctx) (kn : list kentry) (b1 : expr) (k1 n1 : Z) : list (saddr * expr) :=
match kn with
| [] => []
| KDisj c1 m1 c2 m2 :: rest =>
let r := disj_sidesB bc rest b1 k1 n1 in
let r1 := if sub_itvB bc b1 k1 n1 c2 m2 then (c1, m1) :: r else r in
if sub_itvB bc b1 k1 n1 c1 m1 then (c2, m2) :: r1 else r1
| _ :: rest => disj_sidesB bc rest b1 k1 n1
end.
Fixpoint disj_sides_xB (bc : bctx) (kn : list kentry) (b1 : expr) (k1 : Z) (n1 : expr) : list (saddr * expr) :=
match kn with
| [] => []
| KDisj c1 m1 c2 m2 :: rest =>
let r := disj_sides_xB bc rest b1 k1 n1 in
let r1 := if sub_itv_xB bc b1 k1 n1 c2 m2 then (c1, m1) :: r else r in
if sub_itv_xB bc b1 k1 n1 c1 m1 then (c2, m2) :: r1 else r1
| _ :: rest => disj_sides_xB bc rest b1 k1 n1
end.
Fixpoint in_sidesB (bc : bctx) (D : list (saddr * expr)) (b2 : expr) (k2 n2 : Z) : bool :=
match D with
| [] => false
| (c, m) :: r => if sub_itvB bc b2 k2 n2 c m then true else in_sidesB bc r b2 k2 n2
end.
Fixpoint in_sides_xB (bc : bctx) (D : list (saddr * expr)) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
match D with
| [] => false
| (c, m) :: r => if sub_itv_xB bc b2 k2 n2 c m then true else in_sides_xB bc r b2 k2 n2
end.
Definition xinside_numB_br (bc : bctx) (br1 : option (Z * Z)) (b1 : expr) (k1 : Z) (n1 : expr) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
match xloB bc b2, xhiB bc b2 with
| Some lo2, Some hi2 =>
if Z.eqb lo2 hi2 then
match br1, xhiB bc n1, xloB bc n2 with
| Some (lo1, hi1), Some h1, Some l2 => Z.leb (lo2 + k2) (lo1 + k1) && Z.leb (hi1 + k1 + h1) (lo2 + k2 + l2)
| _, _, _ => false
end
else false
| _, _ => false
end.
Definition xinsideB_br (bc : bctx) (br1 : option (Z * Z)) (b1 : expr) (k1 : Z) (n1 : expr) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
if shares_var b1 b2 then xinside0B bc b1 k1 n1 b2 k2 n2
else if novars b2 then
(if xinside_numB_br bc br1 b1 k1 n1 b2 k2 n2 then true
else match n1 with ELit _ => false | _ => xinside0B bc b1 k1 n1 b2 k2 n2 end)
else false.
Definition sub_itvB_br (bc : bctx) (br : option (Z * Z)) (b : expr) (k n : Z) (c : saddr) (m : expr) : bool :=
if (if (expr_eqb b (a_base c) && Z.leb (a_off c) k)%bool then
match xloB bc m with Some ml => Z.leb (k + n) (a_off c + ml) | None => false end
else false)
then true
else if (Z.leb 0 n && Z.ltb n two64)%bool then xinsideB_br bc br b k (ELit n) (a_base c) (a_off c) m else false.
Definition sub_itv_xB_br (bc : bctx) (br : option (Z * Z)) (b : expr) (k : Z) (n : expr) (c : saddr) (m : expr) : bool :=
xinsideB_br bc br b k n (a_base c) (a_off c) m.
Fixpoint disj_sidesB_br (bc : bctx) (br : option (Z * Z)) (kn : list kentry) (b1 : expr) (k1 n1 : Z) : list (saddr * expr) :=
match kn with
| [] => []
| KDisj c1 m1 c2 m2 :: rest =>
let r := disj_sidesB_br bc br rest b1 k1 n1 in
let r1 := if sub_itvB_br bc br b1 k1 n1 c2 m2 then (c1, m1) :: r else r in
if sub_itvB_br bc br b1 k1 n1 c1 m1 then (c2, m2) :: r1 else r1
| _ :: rest => disj_sidesB_br bc br rest b1 k1 n1
end.
Fixpoint disj_sides_xB_br (bc : bctx) (br : option (Z * Z)) (kn : list kentry) (b1 : expr) (k1 : Z) (n1 : expr) : list (saddr * expr) :=
match kn with
| [] => []
| KDisj c1 m1 c2 m2 :: rest =>
let r := disj_sides_xB_br bc br rest b1 k1 n1 in
let r1 := if sub_itv_xB_br bc br b1 k1 n1 c2 m2 then (c1, m1) :: r else r in
if sub_itv_xB_br bc br b1 k1 n1 c1 m1 then (c2, m2) :: r1 else r1
| _ :: rest => disj_sides_xB_br bc br rest b1 k1 n1
end.
Fixpoint in_sidesB_br (bc : bctx) (br : option (Z * Z)) (D : list (saddr * expr)) (b2 : expr) (k2 n2 : Z) : bool :=
match D with
| [] => false
| (c, m) :: r => if sub_itvB_br bc br b2 k2 n2 c m then true else in_sidesB_br bc br r b2 k2 n2
end.
Fixpoint in_sides_xB_br (bc : bctx) (br : option (Z * Z)) (D : list (saddr * expr)) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
match D with
| [] => false
| (c, m) :: r => if sub_itv_xB_br bc br b2 k2 n2 c m then true else in_sides_xB_br bc br r b2 k2 n2
end.
Definition mk_sprepB (bc : bctx) (b1 : expr) (k1 : Z) (n1 : expr) : sprep :=
let br := base_rangeB bc b1 in
SPrep br (xhiB bc n1)
(match n1 with ELit z1 => disj_sidesB_br bc br (bc_fk bc) b1 k1 (zlit64 z1) | _ => [] end)
(disj_sides_xB_br bc br (bc_fk bc) b1 k1 n1).
Definition ranges_apart_pB (bc : bctx) (sp : sprep) (b1 : expr) (k1 : Z) (n1 : expr)
(b2 : expr) (k2 : Z) (n2 : expr) : bool :=
let br2 := base_rangeB bc b2 in
match n1, n2 with
| ELit z1, ELit z2 =>
let m1 := zlit64 z1 in let m2 := zlit64 z2 in
if expr_eqb b2 b1 then (Z.leb (k1 + m1) k2 || Z.leb (k2 + m2) k1)%bool else
if (match sp_rng sp, br2 with
| Some (lo1, hi1), Some (lo2, hi2) =>
(Z.leb (hi1 + k1 + m1) (lo2 + k2) || Z.leb (hi2 + k2 + m2) (lo1 + k1))%bool
| _, _ => false
end) then true
else if in_sidesB_br bc br2 (sp_D sp) b2 k2 m2 then true
else lin_apartB bc b1 k1 m1 b2 k2 m2
| _, _ =>
if (match sp_rng sp, br2, sp_h1 sp, xhiB bc n2 with
| Some (lo1, hi1), Some (lo2, hi2), Some h1, Some h2 =>
if (Z.leb (hi1 + k1 + h1) (lo2 + k2) || Z.leb (hi2 + k2 + h2) (lo1 + k1))%bool then true
else
if match end_hiB bc b1 k1 n1 lo1 hi1 h1 with Some e1 => Z.leb e1 (lo2 + k2) | None => false end then true
else match end_hiB bc b2 k2 n2 lo2 hi2 h2 with Some e2 => Z.leb e2 (lo1 + k1) | None => false end
| _, _, _, _ => false
end) then true
else if in_sides_xB_br bc br2 (sp_Dx sp) b2 k2 n2 then true
else if negb (shares_var b1 b2) then false
else if lin_ge0B bc [(b2, k2)] [(b1, k1); (n1, 0%Z)] then true
else lin_ge0B bc [(b1, k1)] [(b2, k2); (n2, 0%Z)]
end.
Lemma lin_test_relB_eqf : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "H'8'XO%211'E'K'>'X<%2231%811'4p061p071poB13poD51pj0:1&TM&UBr1%211%411&YI%114%C3831pjDE1").
Proof. intros. bcfe. unfold lin_test_relB, lin_test_rel. (repeat first [ rewrite bc_fs_mkbc | rewrite erangeB_eqf ]). reflexivity. Qed.
#[export] Hint Rewrite lin_test_relB_eqf : bceq.
Lemma lin_testB_eqf : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "H'8'XO%211'E'K'>'X<%2231%811'4p061p071poB13poD51pj0:1&TL&UBr1%211%411&YH%114%C3831pjDE1").
Proof. intros. bcfe. unfold lin_testB, lin_test. (repeat first [ rewrite erangeB_eqf | rewrite lin_test_relB_eqf ]). reflexivity. Qed.
#[export] Hint Rewrite lin_testB_eqf : bceq.
Lemma lin_srangeB_eqf : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "D'8'XO%211'E'X<';'>'K%2211%411pj>61&TK&UBr1%211%411&YG%114%?3831pjDA1").
Proof. intros. bcfe. unfold lin_srangeB, lin_srange. (repeat first [ rewrite erangeB_eqf | rewrite srl_expandB_eqf ]). reflexivity. Qed.
#[export] Hint Rewrite lin_srangeB_eqf : bceq.
Lemma lin_nowrapRB_eqf : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "@'8'XO%211'E'X<'4pj>21&TI&UBr1%211%411&YD%114%;3831pjD=1").
Proof. intros. bcfe. unfold lin_nowrapRB, lin_nowrapR. (repeat first [ rewrite srl_expandB_eqf | rewrite lin_testB_eqf | rewrite lin_srangeB_eqf ]). reflexivity. Qed.
#[export] Hint Rewrite lin_nowrapRB_eqf : bceq.
Lemma lin_apart0B_eqf : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "F'8'XO%211'E'X<'K'4pm821pl231pi>51pm651pl061pi<81&TA&UBr1%211%411&Y=%114%A3831pjDC1").
Proof. intros. bcfe. unfold lin_apart0B, lin_apart0. (repeat first [ rewrite lin_testB_eqf | rewrite lin_nowrapRB_eqf ]). reflexivity. Qed.
#[export] Hint Rewrite lin_apart0B_eqf : bceq.
Lemma lin_apartB_eqf : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "F'8'XO%211'E'X<'K'4pm821pl231pi>51pm651pl061pi<81&TB&UBr1%211%411&Y<%114%A3831pjDC1").
Proof. intros. bcfe. unfold lin_apartB, lin_apart. (repeat first [ rewrite lin_apart0B_eqf ]). reflexivity. Qed.
#[export] Hint Rewrite lin_apartB_eqf : bceq.
Lemma lin_brangeB_eqf : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "D'8'XO%211'E'X<';'>'K%2211%411pj>61&TD&UBr1%211%411&Y?%114%?3831pjDA1").
Proof. intros. bcfe. unfold lin_brangeB, lin_brange. (repeat first [ rewrite bc_fs_mkbc | rewrite erangeB_eqf ]). reflexivity. Qed.
#[export] Hint Rewrite lin_brangeB_eqf : bceq.
Lemma xloB_eqf : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "B'8'XO%211'E'X<';'K%211pj>41&W9&UBr1%211%411&[L%114%=3831pjD?1").
Proof. intros. bcfe. unfold xloB, xlo. (repeat first [ rewrite erangeB_eqf | rewrite lin_srangeB_eqf | rewrite lin_brangeB_eqf ]). reflexivity. Qed.
#[export] Hint Rewrite xloB_eqf : bceq.
Lemma xhiB_eqf : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "B'8'XO%211'E'X<';'K%211pj>41&W3&UBr1%211%411&[F%114%=3831pjD?1").
Proof. intros. bcfe. unfold xhiB, xhi. (repeat first [ rewrite erangeB_eqf | rewrite lin_srangeB_eqf | rewrite lin_brangeB_eqf ]). reflexivity. Qed.
#[export] Hint Rewrite xhiB_eqf : bceq.
Lemma xt_nowrapB_eqf : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "@'8'XO%211'E&[N'4poD21&W:&UBr1%211%411&[M%114%;3831pjD=1").
Proof.
intros fk. apply functional_extensionality; intros ts.
induction ts as [|[e k] rest IH]; intros; bcfe; [reflexivity|].
cbn [xt_nowrapB xt_nowrap]. rewrite IH. (repeat first [ rewrite lin_nowrapRB_eqf ]). reflexivity.
Qed.
#[export] Hint Rewrite xt_nowrapB_eqf : bceq.
Lemma lin_ge0_scaledB_eqf : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "E'8'XO%211'E'K'>'X<%2231%811'4poD21pj071&TF&UBr1%211%411&YA%114%@3831pjDB1").
Proof. intros. bcfe. unfold lin_ge0_scaledB, lin_ge0_scaled. (repeat first [ rewrite srl_expandB_eqf | rewrite lin_testB_eqf ]). reflexivity. Qed.
#[export] Hint Rewrite lin_ge0_scaledB_eqf : bceq.
Lemma lin_ge0B_eqf : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "A'8'XO%211'E&[N'4pm:21pmH31&TE&UBr1%211%411&Y@%114%<3831pjD>1").
Proof. intros. bcfe. unfold lin_ge0B, lin_ge0. (repeat first [ rewrite ealignB_eqf | rewrite srl_expandB_eqf | rewrite lin_testB_eqf | rewrite xt_nowrapB_eqf | rewrite lin_ge0_scaledB_eqf ]). reflexivity. Qed.
#[export] Hint Rewrite lin_ge0B_eqf : bceq.
Lemma xinside0B_eqf : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "F'8'XO%211'E'X<'K'4pm831pl231pi>51pm661pl061pi<81&W4&UBr1%211%411&[H%114%A3831pjDC1").
Proof. intros. bcfe. unfold xinside0B, xinside0. (repeat first [ rewrite lin_ge0B_eqf ]). reflexivity. Qed.
#[export] Hint Rewrite xinside0B_eqf : bceq.
Lemma xinside_numB_eqf : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "F'8'XO%211'E'X<'K'4pm831pl231pi>51pm661pl061pi<81&W7&UBr1%211%411&[J%114%A3831pjDC1").
Proof. intros. bcfe. unfold xinside_numB, xinside_num. (repeat first [ rewrite base_rangeB_eqf | rewrite xloB_eqf | rewrite xhiB_eqf ]). reflexivity. Qed.
#[export] Hint Rewrite xinside_numB_eqf : bceq.
Lemma xinsideB_eqf : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "F'8'XO%211'E'X<'K'4pm831pl231pi>51pm661pl061pi<81&W5&UBr1%211%411&[G%114%A3831pjDC1").
Proof. intros. bcfe. unfold xinsideB, xinside. (repeat first [ rewrite xinside0B_eqf | rewrite xinside_numB_eqf ]). reflexivity. Qed.
#[export] Hint Rewrite xinsideB_eqf : bceq.
Lemma sub_itvB_eqf : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "F'8'XO%211'E'X<'K'ZK'4pm041pj031pm451pkL61pi:81&V?&UBr1%211%411&[5%114%A3831pjDC1").
Proof. intros. bcfe. unfold sub_itvB, sub_itv. (repeat first [ rewrite xloB_eqf | rewrite xinsideB_eqf ]). reflexivity. Qed.
#[export] Hint Rewrite sub_itvB_eqf : bceq.
Lemma kdisj_apartB_eqf : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "G'8'XO%211'E'X<'K'4pm821pl231pi>51pm651pl061pi<81pl:;1&SN&UBr1%211%411&XM%114%B3831pjDD1").
Proof.
intros fk. apply functional_extensionality; intros kn. apply functional_extensionality; intros b1. apply functional_extensionality; intros k1. apply functional_extensionality; intros n1. apply functional_extensionality; intros b2. apply functional_extensionality; intros k2. apply functional_extensionality; intros n2.
revert b1 k1 n1 b2 k2 n2. induction kn as [|K rest IH]; intros; bcfe; [reflexivity|].
cbn [kdisj_apartB kdisj_apart]. rewrite IH. (repeat first [ rewrite sub_itvB_eqf ]). reflexivity.
Qed.
#[export] Hint Rewrite kdisj_apartB_eqf : bceq.
Lemma ranges_apartB_eqf : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "F'8'XO%211'E'X<'K'4pm821pl231pi>51pm651pl061pi<81&V5&UBr1%211%411&ZE%114%A3831pjDC1").
Proof. intros. bcfe. unfold ranges_apartB, ranges_apart. (repeat first [ rewrite bc_fk_mkbc | rewrite base_rangeB_eqf | rewrite lin_apartB_eqf | rewrite kdisj_apartB_eqf ]). reflexivity. Qed.
#[export] Hint Rewrite ranges_apartB_eqf : bceq.
Lemma sub_itv_xB_eqf : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "F'8'XO%211'E'X<'K'ZK'4pm041pj031pm461pkL61pi:81&VA&UBr1%211%411&[7%114%A3831pjDC1").
Proof. intros. bcfe. unfold sub_itv_xB, sub_itv_x. (repeat first [ rewrite xinsideB_eqf ]). reflexivity. Qed.
#[export] Hint Rewrite sub_itv_xB_eqf : bceq.
Lemma kdisj_apart_xB_eqf : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "G'8'XO%211'E'X<'K'4pm831pl231pi>51pm661pl061pi<81pl:;1&SO&UBr1%211%411&XN%114%B3831pjDD1").
Proof.
intros fk. apply functional_extensionality; intros kn. apply functional_extensionality; intros b1. apply functional_extensionality; intros k1. apply functional_extensionality; intros n1. apply functional_extensionality; intros b2. apply functional_extensionality; intros k2. apply functional_extensionality; intros n2.
revert b1 k1 n1 b2 k2 n2. induction kn as [|K rest IH]; intros; bcfe; [reflexivity|].
cbn [kdisj_apart_xB kdisj_apart_x]. rewrite IH. (repeat first [ rewrite sub_itv_xB_eqf ]). reflexivity.
Qed.
#[export] Hint Rewrite kdisj_apart_xB_eqf : bceq.
Lemma end_hiB_eqf : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "G'8'XO%211'E'X<'K';%112pk431pk841plJ51pm471pkL71pi:91&S0&UBr1%211%411&X7%114%B3831pjDD1").
Proof. intros. bcfe. unfold end_hiB, end_hi. (repeat first [ rewrite find_rangeI_mkbc ]). reflexivity. Qed.
#[export] Hint Rewrite end_hiB_eqf : bceq.
Lemma ranges_apart_xB_eqf : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "F'8'XO%211'E'X<'K'4pm831pl231pi>51pm661pl061pi<81&V8&UBr1%211%411&ZH%114%A3831pjDC1").
Proof. intros. bcfe. unfold ranges_apart_xB, ranges_apart_x. (repeat first [ rewrite bc_fk_mkbc | rewrite base_rangeB_eqf | rewrite xhiB_eqf | rewrite lin_ge0B_eqf | rewrite ranges_apartB_eqf | rewrite kdisj_apart_xB_eqf | rewrite end_hiB_eqf ]). reflexivity. Qed.
#[export] Hint Rewrite ranges_apart_xB_eqf : bceq.
Lemma disj_sidesB_eqf : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "G'8'XO%211'E'X<'K'>'ZK%2214%911pm651pl061pi<81pl:;1&RF&UBr1%211%411&X1%114%B3831pjDD1").
Proof.
intros fk. apply functional_extensionality; intros kn. apply functional_extensionality; intros b1. apply functional_extensionality; intros k1. apply functional_extensionality; intros n1.
revert b1 k1 n1. induction kn as [|K rest IH]; intros; bcfe; [reflexivity|].
cbn [disj_sidesB disj_sides]. rewrite IH. (repeat first [ rewrite sub_itvB_eqf ]). reflexivity.
Qed.
#[export] Hint Rewrite disj_sidesB_eqf : bceq.
Lemma disj_sides_xB_eqf : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "G'8'XO%211'E'X<'K'>'ZK%2214%911pm661pl061pi<81pl:;1&RH&UBr1%211%411&X3%114%B3831pjDD1").
Proof.
intros fk. apply functional_extensionality; intros kn. apply functional_extensionality; intros b1. apply functional_extensionality; intros k1. apply functional_extensionality; intros n1.
revert b1 k1 n1. induction kn as [|K rest IH]; intros; bcfe; [reflexivity|].
cbn [disj_sides_xB disj_sides_x]. rewrite IH. (repeat first [ rewrite sub_itv_xB_eqf ]). reflexivity.
Qed.
#[export] Hint Rewrite disj_sides_xB_eqf : bceq.
Lemma in_sidesB_eqf : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "H'8'XO%211'E'>'ZK'X<%3221%811'K'4pm821pl231pi>71pQL61&SE&UBr1%211%411&XE%114%C3831pjDE1").
Proof.
intros fk. apply functional_extensionality; intros D. apply functional_extensionality; intros b2. apply functional_extensionality; intros k2. apply functional_extensionality; intros n2.
revert b2 k2 n2. induction D as [|[c m] rest IH]; intros; bcfe; [reflexivity|].
cbn [in_sidesB in_sides]. rewrite IH. (repeat first [ rewrite sub_itvB_eqf ]). reflexivity.
Qed.
#[export] Hint Rewrite in_sidesB_eqf : bceq.
Lemma in_sides_xB_eqf : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "H'8'XO%211'E'>'ZK'X<%3221%811'K'4pm851pl231pi>71pQL61&SG&UBr1%211%411&XG%114%C3831pjDE1").
Proof.
intros fk. apply functional_extensionality; intros D. apply functional_extensionality; intros b2. apply functional_extensionality; intros k2. apply functional_extensionality; intros n2.
revert b2 k2 n2. induction D as [|[c m] rest IH]; intros; bcfe; [reflexivity|].
cbn [in_sides_xB in_sides_x]. rewrite IH. (repeat first [ rewrite sub_itv_xB_eqf ]). reflexivity.
Qed.
#[export] Hint Rewrite in_sides_xB_eqf : bceq.
Lemma xinside_numB_br_eqf : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "K'8'XO%211'E';'>'K%2211%411'X<'4pm821pl261pi>41pm651pl091pi<71piL91&W8&UBr1%211%411&[K%114%F3831pjDH1").
Proof. intros. bcfe. unfold xinside_numB_br, xinside_num_br. (repeat first [ rewrite xloB_eqf | rewrite xhiB_eqf ]). reflexivity. Qed.
#[export] Hint Rewrite xinside_numB_br_eqf : bceq.
Lemma xinsideB_br_eqf : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "K'8'XO%211'E';'>'K%2211%411'X<'4pm821pl261pi>41pm651pl091pi<71piL91&W6&UBr1%211%411&[I%114%F3831pjDH1").
Proof. intros. bcfe. unfold xinsideB_br, xinside_br. (repeat first [ rewrite xinside0B_eqf | rewrite xinside_numB_br_eqf ]). reflexivity. Qed.
#[export] Hint Rewrite xinsideB_br_eqf : bceq.
Lemma sub_itvB_br_eqf : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "K'8'XO%211'E';'>'K%2211%411'X<'ZK'4pm031pj031pm481pkL91pi:71piJ91&V@&UBr1%211%411&[6%114%F3831pjDH1").
Proof. intros. bcfe. unfold sub_itvB_br, sub_itv_br. (repeat first [ rewrite xloB_eqf | rewrite xinsideB_br_eqf ]). reflexivity. Qed.
#[export] Hint Rewrite sub_itvB_br_eqf : bceq.
Lemma sub_itv_xB_br_eqf : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "K'8'XO%211'E';'>'K%2211%411'X<'ZK'4pm031pj031pm451pkL91pi:71piJ91&VB&UBr1%211%411&[8%114%F3831pjDH1").
Proof. intros. bcfe. unfold sub_itv_xB_br, sub_itv_x_br. (repeat first [ rewrite xinsideB_br_eqf ]). reflexivity. Qed.
#[export] Hint Rewrite sub_itv_xB_br_eqf : bceq.
Lemma disj_sidesB_br_eqf : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "K'8'XO%211'E';'>'K%2211%411'X<'ZK%6212%<11pm671pl081pi<61pl:>1piJ91&RG&UBr1%211%411&X2%114%F3831pjDH1").
Proof.
intros fk. apply functional_extensionality; intros br. apply functional_extensionality; intros kn. apply functional_extensionality; intros b1. apply functional_extensionality; intros k1. apply functional_extensionality; intros n1.
revert b1 k1 n1. induction kn as [|K rest IH]; intros; bcfe; [reflexivity|].
cbn [disj_sidesB_br disj_sides_br]. rewrite IH. (repeat first [ rewrite sub_itvB_br_eqf ]). reflexivity.
Qed.
#[export] Hint Rewrite disj_sidesB_br_eqf : bceq.
Lemma disj_sides_xB_br_eqf : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "K'8'XO%211'E';'>'K%2211%411'X<'ZK%6212%<11pm641pl081pi<61pl:>1piJ91&RI&UBr1%211%411&X4%114%F3831pjDH1").
Proof.
intros fk. apply functional_extensionality; intros br. apply functional_extensionality; intros kn. apply functional_extensionality; intros b1. apply functional_extensionality; intros k1. apply functional_extensionality; intros n1.
revert b1 k1 n1. induction kn as [|K rest IH]; intros; bcfe; [reflexivity|].
cbn [disj_sides_xB_br disj_sides_x_br]. rewrite IH. (repeat first [ rewrite sub_itv_xB_br_eqf ]). reflexivity.
Qed.
#[export] Hint Rewrite disj_sides_xB_br_eqf : bceq.
Lemma in_sidesB_br_eqf : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "L'8'XO%211'E';'>'K%2211%411'ZK'X<%6221%<11'4pm881pl291pi>61pQL51piJ:1&SF&UBr1%211%411&XF%114%G3831pjDI1").
Proof.
intros fk. apply functional_extensionality; intros br. apply functional_extensionality; intros D. apply functional_extensionality; intros b2. apply functional_extensionality; intros k2. apply functional_extensionality; intros n2.
revert b2 k2 n2. induction D as [|[c m] rest IH]; intros; bcfe; [reflexivity|].
cbn [in_sidesB_br in_sides_br]. rewrite IH. (repeat first [ rewrite sub_itvB_br_eqf ]). reflexivity.
Qed.
#[export] Hint Rewrite in_sidesB_br_eqf : bceq.
Lemma in_sides_xB_br_eqf : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "L'8'XO%211'E';'>'K%2211%411'ZK'X<%6221%<11'4pm841pl291pi>61pQL51piJ:1&SH&UBr1%211%411&XH%114%G3831pjDI1").
Proof.
intros fk. apply functional_extensionality; intros br. apply functional_extensionality; intros D. apply functional_extensionality; intros b2. apply functional_extensionality; intros k2. apply functional_extensionality; intros n2.
revert b2 k2 n2. induction D as [|[c m] rest IH]; intros; bcfe; [reflexivity|].
cbn [in_sides_xB_br in_sides_x_br]. rewrite IH. (repeat first [ rewrite sub_itv_xB_br_eqf ]). reflexivity.
Qed.
#[export] Hint Rewrite in_sides_xB_br_eqf : bceq.
Lemma mk_sprepB_eqf : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "C'8'XO%211'E'X<'K'[1pm631pl031pi<51&U@&UBr1%211%411&Z9%114%>3831pjD@1").
Proof. intros. bcfe. unfold mk_sprepB, mk_sprep. (repeat first [ rewrite bc_fk_mkbc | rewrite base_rangeB_eqf | rewrite xhiB_eqf | rewrite disj_sidesB_br_eqf | rewrite disj_sides_xB_br_eqf ]). reflexivity. Qed.
#[export] Hint Rewrite mk_sprepB_eqf : bceq.
Lemma ranges_apart_pB_eqf : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "H'8'XO%211'E'[1'X<'K'4pm831pl231pi>51pm661pl061pi<81pnJ:1&V6&UBr1%211%411&ZF%114%C3831pjDE1").
Proof. intros. bcfe. unfold ranges_apart_pB, ranges_apart_p. (repeat first [ rewrite base_rangeB_eqf | rewrite lin_apartB_eqf | rewrite xhiB_eqf | rewrite lin_ge0B_eqf | rewrite end_hiB_eqf | rewrite in_sidesB_br_eqf | rewrite in_sides_xB_br_eqf ]). reflexivity. Qed.
#[export] Hint Rewrite ranges_apart_pB_eqf : bceq.
Fixpoint coeffs_divkB (bc : bctx) (m : Z) (ts : list (Z * expr)) : bool :=
match ts with
| [] => true
| (k, a) :: rest => ((Z.eqb (k mod m) 0 || Z.eqb ((k * 2 ^ ealignB bc a) mod m) 0) && coeffs_divkB bc m rest)%bool
end.
Definition lin_lowbits_knB (bc : bctx) (e : expr) (k : Z) : option Z :=
let l := lin_of e in
if coeffs_divkB bc (2 ^ k) (snd l) then Some ((fst l) mod 2 ^ k)%Z
else pageup_low e (2 ^ k).
Definition lin_nowrap_lB (bc : bctx) (c : Z) (ts : list (Z * expr)) : bool :=
match lin_range (erangeB bc) c ts with
| Some (lo, hi) => (Z.leb 0 lo && Z.ltb hi two64)%bool
| None => false
end.
Definition mkSrlB (bc : bctx) (a : expr) (s : Z) : expr :=
let l := lin_of a in
let m := (2 ^ s)%Z in
if (negb (lin_trivial l) && coeffs_div m (snd l) && lin_nowrapB bc a)%bool
then unlin ((fst l / m)%Z, ldiv_terms m (snd l))
else
match (if (negb (lin_trivial l) && lin_nowrapB bc a)%bool then lsplit_divc m (snd l) else ([], [])) with
| ((_ :: _) as dts, (_ :: _) as rts) =>
match (if lin_nowrap_lB bc (fst l) rts then erangeB bc (unlin (fst l, rts)) else None) with
| Some (lo, hi) =>
if Z.eqb (lo / m) (hi / m) then unlin ((lo / m)%Z, ldiv_terms m dts)
else mkAlu ALU_SRL a (ELit s)
| None => mkAlu ALU_SRL a (ELit s)
end
| _ => mkAlu ALU_SRL a (ELit s)
end.
Fixpoint lowbitsB (bc : bctx) (e : expr) (j : Z) {struct e} : option Z :=
let m := (2 ^ j)%Z in
let dflt := if Z.leb j (ealignB bc e) then Some 0%Z else lin_lowbits_knB bc e j in
match e with
| ELit z => Some ((z mod two64) mod m)%Z
| EAlu ALU_AND a (ELit c) =>
if Z.eqb ((c mod two64) mod m) 0 then Some 0%Z else
match lowbitsB bc a j with Some v => Some (Z.land v ((c mod two64) mod m)) | None => dflt end
| EAlu ALU_OR a (ELit c) =>
match lowbitsB bc a j with Some v => Some (Z.lor v ((c mod two64) mod m)) | None => dflt end
| EAlu ALU_XOR a (ELit c) =>
match lowbitsB bc a j with Some v => Some (Z.lxor v ((c mod two64) mod m)) | None => dflt end
| EAlu ALU_ADD a b =>
match lowbitsB bc a j, lowbitsB bc b j with Some x, Some y => Some ((x + y) mod m)%Z | _, _ => dflt end
| EAlu ALU_SUB a b =>
match lowbitsB bc a j, lowbitsB bc b j with Some x, Some y => Some ((x - y) mod m)%Z | _, _ => dflt end
| EMd M_MUL (ELit c) a =>
if Z.eqb ((c mod two64) mod m) 0 then Some 0%Z else
match lowbitsB bc a j with Some v => Some ((c * v) mod m)%Z | None => dflt end
| _ => dflt
end.
Fixpoint lsplit_divB (bc : bctx) (m : Z) (ts : list (Z * expr)) : list (Z * expr) * list (Z * expr) :=
match ts with
| [] => ([], [])
| (k, a) :: rest =>
let (d, r) := lsplit_divB bc m rest in
if (Z.eqb (k mod m) 0 || Z.eqb ((k * 2 ^ ealignB bc a) mod m) 0)%bool then ((k, a) :: d, r) else (d, (k, a) :: r)
end.
Definition and_high_splitB (bc : bctx) (bk : expr) (j c : Z) (dts rts : list (Z * expr)) : expr :=
let m := (2 ^ j)%Z in
let cA := (c - c mod m)%Z in
let r := unlin ((c mod m)%Z, rts) in
match erangeB bc r with
| Some (lo, hi) =>
if Z.eqb (lo / m) (hi / m) then unlin ((cA + (lo / m) * m)%Z, dts)
else mkAlu ALU_ADD (unlin (cA, dts)) (mkAlu ALU_AND r bk)
| None => mkAlu ALU_ADD (unlin (cA, dts)) (mkAlu ALU_AND r bk)
end.
Definition and_low_splitB (bc : bctx) (bk : expr) (j c : Z) (rts : list (Z * expr)) : expr :=
let m := (2 ^ j)%Z in
let r := unlin ((c mod m)%Z, rts) in
match erangeB bc r with
| Some (lo, hi) =>
if Z.eqb (lo / m) (hi / m) then unlin ((c mod m - (lo / m) * m)%Z, rts)
else mkAlu ALU_AND r bk
| None => mkAlu ALU_AND r bk
end.
Definition narrow_maskB (bc : bctx) (a : expr) (k' : Z) : option Z :=
let i := ctz64 k' in
let m := (k' + 2 ^ i)%Z in
let j := Z.log2 m in
if (Z.ltb 0 k' && Z.eqb m (2 ^ j) && Z.ltb j 64)%bool then
match xhiB bc a with
| Some h => if Z.ltb h (2 ^ j) then Some (two64 - 2 ^ i)%Z else None
| None => None
end
else None.
Definition mkAnd0B (bc : bctx) (a b : expr) : expr :=
match b with
| ELit k =>
let k' := (k mod two64)%Z in
let j := Z.log2 (two64 - k') in
if (Z.eqb (two64 - k') (2 ^ j) && Z.ltb j 64)%bool then
(if Z.leb j (ealignB bc a) then a
else let l := lin_of a in
if (negb (lin_trivial l) && coeffs_divkB bc (2 ^ j) (snd l))%bool
then unlin ((fst l - (fst l) mod 2 ^ j)%Z, snd l)
else
match (if lin_trivial l then ([], snd l) else lsplit_divB bc (2 ^ j) (snd l)) with
| ((_ :: _) as dts, (_ :: _) as rts) => and_high_splitB bc b j (fst l) dts rts
| _ =>
mkMd M_MUL (ELit (2 ^ j)%Z) (mkSrlB bc a j)
end)
else
let j2 := Z.log2 (k' + 1) in
if (Z.eqb (k' + 1) (2 ^ j2) && Z.ltb j2 64)%bool then
(if Z.leb j2 (ealignB bc a) then ELit 0
else match lowbitsB bc a j2 with
| Some v => ELit v
| None =>
if lin_trivial (lin_of a) then mkAlu ALU_AND a b
else match lin_lowbits_knB bc a j2 with
| Some v => ELit v
| None =>
match lsplit_divB bc (2 ^ j2) (snd (lin_of a)) with
| (_ :: _, (_ :: _) as rts) => and_low_splitB bc b j2 (fst (lin_of a)) rts
| _ => mkAlu ALU_AND a b
end
end
end)
else
let j3 := (Z.log2 k' + 1)%Z in
if (Z.ltb 0 k' && Z.leb j3 64 && negb (lin_trivial (lin_of a)))%bool then
match lin_lowbits_knB bc a j3 with
| Some v => ELit (Z.land v k')
| None => mkAlu ALU_AND a b
end
else mkAlu ALU_AND a b
| _ => mkAlu ALU_AND a b
end.
Definition mkAndB (bc : bctx) (a b : expr) : expr :=
match b with
| ELit k =>
match narrow_maskB bc a (k mod two64)%Z with
| Some m => mkAnd0B bc a (ELit m)
| None => mkAnd0B bc a b
end
| _ => mkAnd0B bc a b
end.
Definition mkAndKB (bc : bctx) (a b : expr) : expr :=
match a, b with
| EAlu ALU_AND x (ELit m1), ELit k => mkAndB bc x (ELit (Z.land (m1 mod two64) (k mod two64))%Z)
| EMd M_MUL (ELit m) (EAlu ALU_SRL x (ELit i)), ELit k =>
let i' := ((i mod two64) mod 64)%Z in
if Z.eqb (m mod two64) (2 ^ i') then mkAndB bc x (ELit (Z.land (two64 - 2 ^ i') (k mod two64))%Z)
else mkAndB bc a b
| _, _ => mkAndB bc a b
end.
Definition or_disjointB (bc : bctx) (a b : expr) : bool :=
match erangeB bc b with
| Some (lo, hi) => (Z.leb 0 lo && Z.ltb hi (2 ^ (ealignB bc a)))%bool
| None => false
end.
Definition mkOrB (bc : bctx) (a b : expr) : expr :=
match is_lit a, is_lit b with
| Some x, Some y => ELit (zalu ALU_OR x y)
| _, _ =>
if or_disjointB bc a b then mkAlu ALU_ADD a b
else if or_disjointB bc b a then mkAlu ALU_ADD a b
else
match b with
| ELit c => mkAlu ALU_ADD (mkAndKB bc a (ELit (Z.lnot (c mod two64)))) (ELit c)
| _ => match a with
| ELit c => mkAlu ALU_ADD (mkAndKB bc b (ELit (Z.lnot (c mod two64)))) (ELit c)
| _ => EAlu ALU_OR a b
end
end
end.
Fixpoint conc_tryB (bc : bctx) (e : expr) (cands : list expr) : option Z :=
match cands with
| [] => None
| s :: rest =>
if closedb s then conc_tryB bc e rest else
if negb (evalS_def s e) then conc_tryB bc e rest else
match erangeB bc s with
| Some (lo, hi) =>
if Z.leb (hi - lo) conc_limit then
match evalS s (wrap64 lo) e with
| Some v =>
if (if Z.ltb hi lo then true
else if probeS s e v hi then probeS s e v (lo + (hi - lo) / 2)%Z else false) then
if all_eval_toS s e v lo (Z.to_nat (hi - lo + 1)) then Some v
else conc_tryB bc e rest
else conc_tryB bc e rest
| None => conc_tryB bc e rest
end
else conc_tryB bc e rest
| None => conc_tryB bc e rest
end
end.
Definition concretizeB (bc : bctx) (e : expr) : option Z :=
if closedb e then eval_closed e else conc_tryB bc e (nubE (subexprs e)).
Definition foldKB (bc : bctx) (e : expr) : expr :=
match e with
| ELit _ => e
| _ => match erangeB bc e with
| Some (lo, hi) => if Z.eqb lo hi then ELit lo
else match concretizeB bc e with Some v => ELit v | None => e end
| None => match concretizeB bc e with Some v => ELit v | None => e end
end
end.
Definition lin_branchB (bc : bctx) (c : branch_cond) (a b : expr) : option bool :=
let ltu := if lin_ge0B bc [(b, (-1)%Z)] [(a, 0%Z)] then Some true
else if lin_ge0B bc [(a, 0%Z)] [(b, 0%Z)] then Some false else None in
match c with
| BC_LTU => ltu
| BC_GEU => option_map negb ltu
| BC_LT | BC_GE =>
match erangeB bc a, erangeB bc b with
| Some (_, ah), Some (_, bh) =>
if (Z.ltb ah (2 ^ 63) && Z.ltb bh (2 ^ 63))%bool
then match c with BC_LT => ltu | _ => option_map negb ltu end
else None
| _, _ => None
end
| BC_EQ | BC_NE =>
if (lin_ge0B bc [(b, (-1)%Z)] [(a, 0%Z)] || lin_ge0B bc [(a, (-1)%Z)] [(b, 0%Z)])%bool
then Some (match c with BC_EQ => false | _ => true end)
else
if (if lin_ge0B bc [(a, 0%Z)] [(b, 0%Z)] then lin_ge0B bc [(b, 0%Z)] [(a, 0%Z)] else false)
then Some (match c with BC_EQ => true | _ => false end)
else None
end.
Definition decide_branchB (bc : bctx) (c : branch_cond) (a b : expr) : option bool :=
match a, b with
| ELit x, ELit y => Some (lit_branch c x y)
| _, _ =>
if expr_eqb a b then Some (cond_on_eq c)
else match diff_branch c a b with
| Some t => Some t
| None =>
match (match erangeB bc a, erangeB bc b with
| Some (al, ah), Some (bl, bh) => range_branch c al ah bl bh
| _, _ => None
end) with
| Some t => Some t
| None => lin_branchB bc c a b
end
end
end.
Definition mkSltB (bc : bctx) (c : branch_cond) (op : aluop) (a b : expr) : expr :=
match a, b with
| ELit _, ELit _ => mkAlu op a b
| _, _ => match decide_branchB bc c a b with
| Some true => ELit 1
| Some false => ELit 0
| None => mkAlu op a b
end
end.
Definition mkAluK0B (bc : bctx) (op : aluop) (a b : expr) : expr :=
match op with
| ALU_SLTU => mkSltB bc BC_LTU ALU_SLTU a b
| ALU_SLT => mkSltB bc BC_LT ALU_SLT a b
| ALU_AND => match a, b with
| ELit _, ELit _ => mkAndB bc a b
| ELit _, _ => mkAndKB bc b a
| _, _ => mkAndKB bc a b
end
| ALU_OR => if expr_eqb a b then a else mkOrB bc a b
| ALU_XOR => if expr_eqb a b then ELit 0 else match is_lit a, b with
| None, ELit k => if Z.eqb (k mod two64) (two64 - 1) then mkAlu ALU_SUB (ELit (two64 - 1)) a
else mkAlu op a b
| _, _ => mkAlu op a b
end
| ALU_SRL => match is_lit a, shamt_of b 6 with
| None, Some s => mkSrlB bc a s
| _, _ => mkAlu op a b
end
| _ => mkAlu op a b
end.
Definition mkAluKB (bc : bctx) (op : aluop) (a b : expr) : expr :=
foldKB bc (mkAluK0B bc op a b).
Definition mkMdKB (bc : bctx) (op : mulop) (a b : expr) : expr :=
match is_lit a, op, b with
| None, M_REMU, ELit m =>
match pow2_log m with
| Some k => mkAluKB bc ALU_AND a (ELit (2 ^ k - 1))
| None => mkMd op a b
end
| None, M_DIVU, ELit m =>
match pow2_log m with
| Some k => mkAluKB bc ALU_SRL a (ELit k)
| None => mkMd op a b
end
| _, _, _ => mkMd op a b
end.
Definition zband32B (bc : bctx) (d : expr) : bool :=
let l := lin_of d in
match lin_range (erangeB bc) (fst l) (snd l) with
| Some (lo, hi) => (Z.ltb (- 2 ^ 31) lo && Z.ltb hi (2 ^ 31))%bool
| None => false
end.
Definition mkAluwK0B (bc : bctx) (op : aluop) (a b : expr) : expr :=
match op with
| ALU_ADD | ALU_SUB =>
let d := mkAlu op a b in
match is_lit d with
| Some v => ELit (zsx32 v)
| None => match erangeB bc d with
| Some (lo, hi) => if sx32_stable lo hi then d else if zband32B bc d then d else mkAluw op a b
| None => if zband32B bc d then d else mkAluw op a b
end
end
| _ => mkAluw op a b
end.
Definition mkAluwKB (bc : bctx) (op : aluop) (a b : expr) : expr :=
foldKB bc (mkAluwK0B bc op a b).
Definition extK0B (bc : bctx) (v : expr) : expr :=
match v with
| EExt sx O n e =>
if Nat.leb n 7 then
match erangeB bc e with
| Some (lo, hi) => if Z.ltb hi (if sx then 2 ^ (8 * Z.of_nat n) / 2 else 2 ^ (8 * Z.of_nat n)) then e else v
| None => v
end
else v
| _ => v
end.
Definition extKB (bc : bctx) (v : expr) : expr := foldKB bc (extK0B bc v).
Definition flat_scB (bc : bctx) (a : saddr) (n : nat) : list sidecond :=
match base_rangeB bc (a_base a) with
| Some (lo, hi) =>
if (Z.leb 0 (lo + a_off a) && Z.leb (hi + a_off a + Z.of_nat n) (2 ^ 64))%bool
then [] else [SCFlat a (elen n)]
| None => [SCFlat a (elen n)]
end.
Fixpoint wr_coveredB (bc : bctx) (kn : list kentry) (a : saddr) (n : nat) : bool :=
match kn with
| [] => false
| KWr (SA kb kk) len :: rest =>
if (if (expr_eqb (a_base a) kb && Z.leb kk (a_off a))%bool
then match xloB bc len with Some l => Z.leb (a_off a + Z.of_nat n) (kk + l) | None => false end
else false)
then true
else if xinsideB bc (a_base a) (a_off a) (ELit (Z.of_nat n)) kb kk len then true
else wr_coveredB bc rest a n
| _ :: rest => wr_coveredB bc rest a n
end.
Fixpoint wr_coveredB_br (bc : bctx) (br : option (Z * Z)) (kn : list kentry) (a : saddr) (n : nat) : bool :=
match kn with
| [] => false
| KWr (SA kb kk) len :: rest =>
if (if (expr_eqb (a_base a) kb && Z.leb kk (a_off a))%bool
then match xloB bc len with Some l => Z.leb (a_off a + Z.of_nat n) (kk + l) | None => false end
else false)
then true
else if xinsideB_br bc br (a_base a) (a_off a) (ELit (Z.of_nat n)) kb kk len then true
else wr_coveredB_br bc br rest a n
| _ :: rest => wr_coveredB_br bc br rest a n
end.
Definition storeok_scB (bc : bctx) (a : saddr) (n : nat) : list sidecond :=
if wr_coveredB_br bc (base_rangeB bc (a_base a)) (bc_fk bc) a n then [] else [SCStoreOk a n].
Definition conc_exprB (bc : bctx) (e : expr) : expr :=
match e with
| ELit _ => e
| _ => match concretizeB bc e with Some v => ELit v | None => e end
end.
Definition enum_branchB (bc : bctx) (c : branch_cond) (a b : expr) : option bool :=
let '(e, pos) := cond_probe c a b in
match concretizeB bc e with
| Some v => let z := Z.eqb (v mod two64) 0 in Some (if pos then negb z else z)
| None => None
end.
Definition to_saddrKB (bc : bctx) (e : expr) (imm : Z) : saddr :=
match split_lit e with
| (ELit _, _) => to_saddr e imm
| _ => match concretizeB bc (mkAlu ALU_ADD e (ELit imm)) with
| Some v => SA (ELit 0) v
| None => to_saddr e imm
end
end.
Definition amo_alignedbB (bc : bctx) (e : expr) (wd : awidth) : bool :=
match lin_lowbits_knB bc e (match wd with AW => 2 | AD => 3 end) with
| Some r => Z.eqb r 0
| None => false
end.
Definition amo_newvalB (bc : bctx) (wd : awidth) (aop : option aluop) (old src : expr) : expr :=
match aop with
| None => src
| Some o => match wd with AW => mkAluwKB bc o old src | AD => mkAluKB bc o old src end
end.
Fixpoint log_lookupB (bc : bctx) (log : list sentry) (rb : expr) (rk : Z) (n : nat) (sx : bool)
(hints : list bool) (acc : list sidecond) : lres :=
match log with
| [] => LMiss acc hints
| SE (SA kb kk) w v :: rest =>
match rel_lit rb rk (Z.of_nat n) kb kk (Z.of_nat w) with
| RInside d => LHit (mkExt sx (Z.to_nat d) n v) acc hints
| RDisjoint => log_lookupB bc rest rb rk n sx hints acc
| RPartial => match log_bytes_lit log rb rk n with
| Some bs => LHit (lit_of_bytes sx n bs) acc hints
| None => LStuck
end
| RUnknown =>
if ranges_apartB bc rb rk (Z.of_nat n) kb kk (Z.of_nat w)
then log_lookupB bc rest rb rk n sx hints acc
else
match hints with
| false :: _ => LStuck
| _ => log_lookupB bc rest rb rk n sx (tl hints)
(SCDisj (SA rb rk) (elen n) (SA kb kk) (elen w) :: acc)
end
end
end.
Fixpoint know_lookupA0B (bc : bctx) (segs : list Segment) (kn : list kentry) (rb : expr) (rk : Z)
(n : nat) (sx : bool) (hints : list bool) (acc : list sidecond) : lres :=
let know_lookup := know_lookupA0B bc in
match kn with
| [] => LMiss acc hints
| K :: rest =>
match K with
| KWord (SA kb kk) w v =>
match rel_lit rb rk (Z.of_nat n) kb kk (Z.of_nat w) with
| RInside d => LHit (mkExt sx (Z.to_nat d) n v) acc hints
| _ => know_lookup segs rest rb rk n sx hints acc
end
| KZero (SA kb kk) len =>
match len with
| ELit l0 =>
match rel_lit rb rk (Z.of_nat n) kb kk (l0 mod 2^64)%Z with
| RInside _ => LHit (ELit 0) acc hints
| RDisjoint | RPartial => know_lookup segs rest rb rk n sx hints acc
| RUnknown =>
if xinsideB bc rb rk (elen n) kb kk len then LHit (ELit 0) acc hints else
match hints with
| true :: hs => LHit (ELit 0) (SCInside (SA rb rk) (elen n) (SA kb kk) len :: acc) hs
| false :: hs => know_lookup segs rest rb rk n sx hs acc
| [] => know_lookup segs rest rb rk n sx [] acc
end
end
| _ =>
if xinsideB bc rb rk (elen n) kb kk len then LHit (ELit 0) acc hints else
match hints with
| true :: hs => LHit (ELit 0) (SCInside (SA rb rk) (elen n) (SA kb kk) len :: acc) hs
| false :: hs => know_lookup segs rest rb rk n sx hs acc
| [] => know_lookup segs rest rb rk n sx [] acc
end
end
| KFill (SA kb kk) len c =>
let hit := fill_lit sx n c in
match len with
| ELit l0 =>
match rel_lit rb rk (Z.of_nat n) kb kk (l0 mod 2^64)%Z with
| RInside _ => LHit hit acc hints
| RDisjoint | RPartial => know_lookup segs rest rb rk n sx hints acc
| RUnknown =>
if xinsideB bc rb rk (elen n) kb kk len then LHit hit acc hints else
match hints with
| true :: hs => LHit hit (SCInside (SA rb rk) (elen n) (SA kb kk) len :: acc) hs
| false :: hs => know_lookup segs rest rb rk n sx hs acc
| [] => know_lookup segs rest rb rk n sx [] acc
end
end
| _ =>
if xinsideB bc rb rk (elen n) kb kk len then LHit hit acc hints else
match hints with
| true :: hs => LHit hit (SCInside (SA rb rk) (elen n) (SA kb kk) len :: acc) hs
| false :: hs => know_lookup segs rest rb rk n sx hs acc
| [] => know_lookup segs rest rb rk n sx [] acc
end
end
| KUnk _ _ => know_lookup segs rest rb rk n sx hints acc
| KBlob (SA kb kk) len k =>
if expr_eqb rb kb then
if Z.leb kk rk then
match len with
| ELit l0 =>
if Z.leb (rk + Z.of_nat n) (kk + (l0 mod 2^64)%Z)
then LHit (EBlob sx k (rk - kk) n) acc hints
else if Z.leb (kk + (l0 mod 2^64)%Z) rk then know_lookup segs rest rb rk n sx hints acc
else LStuck
| _ =>
if match erangeB bc len with
| Some (lo, _) => Z.leb (rk + Z.of_nat n) (kk + lo)
| None => false
end
then LHit (EBlob sx k (rk - kk) n) acc hints
else
match hints with
| true :: hs => LHit (EBlob sx k (rk - kk) n)
(SCInside (SA rb rk) (elen n) (SA kb kk) len :: acc) hs
| false :: hs => know_lookup segs rest rb rk n sx hs acc
| [] => know_lookup segs rest rb rk n sx [] acc
end
end
else know_lookup segs rest rb rk n sx hints acc
else know_lookup segs rest rb rk n sx hints acc
| KImg lo hi =>
match rb with
| ELit 0 =>
if (Z.leb lo rk && Z.leb (rk + Z.of_nat n) hi)%bool then
match img_bytes segs rk n with
| Some bs => LHit (lit_of_bytes sx n bs) acc hints
| None => LStuck
end
else know_lookup segs rest rb rk n sx hints acc
| _ => know_lookup segs rest rb rk n sx hints acc
end
| KAlign _ _ => know_lookup segs rest rb rk n sx hints acc
| KRange _ _ _ => know_lookup segs rest rb rk n sx hints acc
| KWr _ _ => know_lookup segs rest rb rk n sx hints acc
| KDisj _ _ _ _ => know_lookup segs rest rb rk n sx hints acc
end
end.
Definition know_lookupAB (bc : bctx) (segs : list Segment) (kn : list kentry) (rb : expr) (rk : Z)
(n : nat) (sx : bool) (hints : list bool) (acc : list sidecond) : lres :=
match know_lookupA0B bc segs kn rb rk n sx hints acc with
| LMiss acc' hints' =>
match know_bytes_lit segs kn rb rk n with
| Some bs => LHit (lit_of_bytes sx n bs) acc' hints'
| None => LMiss acc' hints'
end
| r => r
end.
Definition sym_readB (segs : list Segment) (ss : sym_state) (bc : bctx) (scr : scripts)
(a : saddr) (n : nat) (sx' : bool)
: option (expr * list sidecond * scripts * nat) :=
match log_lookupB bc (s_log ss) (a_base a) (a_off a) n sx' (sc_hints scr) [] with
| LStuck => None
| LHit v scs hints =>
Some (extKB bc v, flat_scB bc a n ++ scs, SCR (sc_dirs scr) (sc_reads scr) hints, s_next ss)
| LMiss scs hints =>
match know_lookupAB bc segs (s_know ss) (a_base a) (a_off a) n sx' hints scs with
| LStuck => None
| LHit v scs' hints' =>
Some (extKB bc v, flat_scB bc a n ++ scs', SCR (sc_dirs scr) (sc_reads scr) hints', s_next ss)
| LMiss scs' hints' =>
let i := s_next ss in
let rv := match sc_reads scr with [] => EVar i | e :: _ => e end in
let reads' := match sc_reads scr with [] => [] | _ :: t => t end in
Some (rv, flat_scB bc a n ++ SCReadBase a n sx' rv :: scs', SCR (sc_dirs scr) reads' hints', S i)
end
end.
Definition sym_stepB (bc : bctx) (segs : list Segment) (i : instr) (ss : sym_state) (scr : scripts) : stepres :=
let g r := sr_get (s_regs ss) r in
let p := s_pc ss in
match i with
| OpImm op rd rs imm => SOk (sset ss rd (mkAluKB bc op (g rs) (ELit (bv_signed imm))) (p + 4)) [] scr
| ShiftImm op rd rs sh => SOk (sset ss rd (mkAluKB bc op (g rs) (ELit (bv_unsigned sh))) (p + 4)) [] scr
| Op op rd rs1 rs2 => SOk (sset ss rd (mkAluKB bc op (g rs1) (g rs2)) (p + 4)) [] scr
| OpImm32 rd rs imm => SOk (sset ss rd (mkAluwKB bc ALU_ADD (g rs) (ELit (bv_signed imm))) (p + 4)) [] scr
| ShiftImm32 op rd rs sh => SOk (sset ss rd (mkAluw op (g rs) (ELit (bv_unsigned sh))) (p + 4)) [] scr
| Op32 op rd rs1 rs2 => SOk (sset ss rd (mkAluwKB bc op (g rs1) (g rs2)) (p + 4)) [] scr
| Mul op rd rs1 rs2 => SOk (sset ss rd (mkMdKB bc op (g rs1) (g rs2)) (p + 4)) [] scr
| Mul32 op rd rs1 rs2 => SOk (sset ss rd (mkMdw op (g rs1) (g rs2)) (p + 4)) [] scr
| Lui rd imm => SOk (sset ss rd (ELit (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_signed imm) 12)))) (p + 4)) [] scr
| Auipc rd imm => SOk (sset ss rd (ELit (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_signed imm) 12 + p)))) (p + 4)) [] scr
| Jal rd imm => SOk (sset ss rd (ELit (p + 4)) (bv_unsigned (Z_to_bv 64 (p + bv_signed imm)))) [] scr
| Jalr rd rs1 imm =>
match conc_exprB bc (g rs1) with
| ELit z => SOk (sset ss rd (ELit (p + 4)) (Z.land (bv_wrap 64 z + bv_signed imm) (-2) mod 2^64)) [] scr
| _ => SStop
end
| Branch c rs1 rs2 imm =>
let tk := bv_unsigned (Z_to_bv 64 (p + bv_signed imm)) in
let a := g rs1 in let b := g rs2 in
match match decide_branchB bc c a b with
| Some t => Some t
| None => match decide_branchB bc c (conc_exprB bc a) (conc_exprB bc b) with
| Some t => Some t
| None => enum_branchB bc c a b
end
end with
| Some t => SOk (sjump ss (if t then tk else p + 4)) [] scr
| None =>
match sc_dirs scr with
| [] => SStop
| t :: dirs' =>
SOk (sjump ss (if t then tk else p + 4)) [SCBr t c a b]
(SCR dirs' (sc_reads scr) (sc_hints scr))
end
end
| Fence _ _ _ _ _ => SOk (sjump ss (p + 4)) [] scr
| FenceI _ _ _ => SOk (sjump ss (p + 4)) [] scr
| Load sz sx rd rs imm =>
let n := msize_bytes sz in
let sx' := match sz with SZ8 => false | _ => sx end in
let a := to_saddrKB bc (g rs) (bv_signed imm) in
match sym_readB segs ss bc scr a n sx' with
| None => SStop
| Some (v, scs, scr', nx') =>
SOk (SSR (p + 4) (if bv_eqb rd 0 then s_regs ss else sr_upd (s_regs ss) (ridx rd) v)
(s_log ss) (s_know ss) nx' (s_resv ss)) scs scr'
end
| Store sz rs1 rs2 imm =>
let n := msize_bytes sz in
let a := to_saddrKB bc (g rs1) (bv_signed imm) in
match resv_inval (s_resv ss) a with
| None => SStop
| Some r' =>
SOk (SSR (p + 4) (s_regs ss) (SE a n (g rs2) :: s_log ss) (s_know ss) (s_next ss) r')
(flat_scB bc a n ++ storeok_scB bc a n) scr
end
| Lr wd _ _ rd rs =>
let n := msize_bytes (amo_sz wd) in
let e := g rs in
if amo_alignedbB bc e wd then
let a := to_saddrKB bc e 0 in
match sym_readB segs ss bc scr a n (amo_sx wd) with
| None => SStop
| Some (v, scs, scr', nx') =>
SOk (SSR (p + 4) (if bv_eqb rd 0 then s_regs ss else sr_upd (s_regs ss) (ridx rd) v)
(s_log ss) (s_know ss) nx' (Some a)) scs scr'
end
else SStop
| Sc wd _ _ rd rs1 rs2 =>
let n := msize_bytes (amo_sz wd) in
let e := g rs1 in
if amo_alignedbB bc e wd then
let a := to_saddrKB bc e 0 in
match s_resv ss with
| Some r =>
if saddr_eqb r a then
SOk (SSR (p + 4) (if bv_eqb rd 0 then s_regs ss else sr_upd (s_regs ss) (ridx rd) (ELit 0))
(SE a n (g rs2) :: s_log ss) (s_know ss) (s_next ss) None)
(flat_scB bc a n ++ storeok_scB bc a n) scr
else SStop
| None => SStop
end
else SStop
| Amo op wd _ _ rd rs1 rs2 =>
match amo_aluop op with
| None => SStop
| Some aop =>
let n := msize_bytes (amo_sz wd) in
let e := g rs1 in
if amo_alignedbB bc e wd then
let a := to_saddrKB bc e 0 in
match resv_inval (s_resv ss) a with
| None => SStop
| Some r' =>
match sym_readB segs ss bc scr a n (amo_sx wd) with
| None => SStop
| Some (vold, scs, scr', nx') =>
SOk (SSR (p + 4) (if bv_eqb rd 0 then s_regs ss else sr_upd (s_regs ss) (ridx rd) vold)
(SE a n (amo_newvalB bc wd aop vold (g rs2)) :: s_log ss) (s_know ss) nx' r')
(scs ++ storeok_scB bc a n) scr'
end
end
else SStop
end
| _ => SStop
end.
Definition know_lookupB (segs : list Segment) (bc : bctx) (rb : expr) (rk : Z)
(n : nat) (sx : bool) (hints : list bool) (acc : list sidecond) : lres :=
know_lookupAB bc segs (bc_fk bc) rb rk n sx hints acc.
Local Open Scope Z_scope.
Definition gran (a : Z) : Z := Z.shiftr a 12.
Definition is_lit0 (e : expr) : bool := match e with ELit 0 => true | _ => false end.
Definition lit0_extent (K : kentry) : option (Z * Z) :=
match K with
| KWord (SA (ELit 0) kk) w _ => Some (kk, kk + Z.of_nat w)
| KZero (SA (ELit 0) kk) (ELit l0) => Some (kk, kk + zmod64 l0)
| KFill (SA (ELit 0) kk) (ELit l0) _ => Some (kk, kk + zmod64 l0)
| KBlob (SA (ELit 0) kk) (ELit l0) _ => Some (kk, kk + zmod64 l0)
| KImg lo hi => Some (lo, hi)
| _ => None
end.
Definition ext_fits (s e : Z) : bool := if Z.ltb s e then Z.leb (gran (e - 1) - gran s) 1 else false.
Definition ext_has (s e g : Z) : bool := if Z.eqb g (gran s) then true else Z.eqb g (gran (e - 1)).
Definition kx_wide0 (K : kentry) : bool :=
match lit0_extent K with
| Some (s, e) => negb (ext_fits s e)
| None =>
match K with
| KZero (SA kb _) _ | KFill (SA kb _) _ _ => true
| KBlob (SA kb _) _ _ => is_lit0 kb
| _ => false
end
end.
Definition kx_cand0 (g : Z) (K : kentry) : bool :=
match lit0_extent K with
| Some (s, e) => if ext_fits s e then ext_has s e g else true
| None => kx_wide0 K
end.
Definition kx_candf (K : kentry) : bool :=
match K with
| KWord (SA kb _) _ _ | KBlob (SA kb _) _ _ => negb (is_lit0 kb)
| KZero _ _ | KFill _ _ _ => true
| _ => false
end.
Definition kx_gkey (g : Z) : positive := match g with Z0 => xH | Zpos p => xO p | Zneg p => xI p end.
Record kix : Type := KX {
kx_kn : list kentry;
kx_w0 : list (positive * kentry);
kx_gran : ptree (list (positive * kentry));
kx_wf : list kentry
}.
Definition kx_bucket (t : ptree (list (positive * kentry))) (g : Z) : list (positive * kentry) :=
match pt_get t (kx_gkey g) with Some b => b | None => [] end.
Definition kx_add (g : Z) (x : positive * kentry) (t : ptree (list (positive * kentry))) : ptree (list (positive * kentry)) :=
pt_set (kx_gkey g) (x :: kx_bucket t g) t.
Fixpoint kx_build (kn : list kentry) (i : positive) : list (positive * kentry) * ptree (list (positive * kentry)) * list kentry :=
match kn with
| [] => ([], PTLeaf, [])
| K :: rest =>
let '(w0, gr, wf) := kx_build rest (Pos.succ i) in
let wf' := if kx_candf K then K :: wf else wf in
match lit0_extent K with
| Some (s, e) =>
if ext_fits s e then
let g1 := gran s in let g2 := gran (e - 1) in
let gr1 := kx_add g1 (i, K) gr in
(w0, (if Z.eqb g1 g2 then gr1 else kx_add g2 (i, K) gr1), wf')
else ((i, K) :: w0, gr, wf')
| None => if kx_wide0 K then ((i, K) :: w0, gr, wf') else (w0, gr, wf')
end
end.
Definition mk_kix (kn : list kentry) : kix :=
let r := kx_build kn xH in KX kn (fst (fst r)) (snd (fst r)) (snd r).
Fixpoint kx_merge (l1 : list (positive * kentry)) : list (positive * kentry) -> list kentry :=
match l1 with
| [] => fun l2 => List.map snd l2
| (p1, K1) :: r1 =>
fix go (l2 : list (positive * kentry)) : list kentry :=
match l2 with
| [] => K1 :: List.map snd r1
| (p2, K2) :: r2 => if Pos.ltb p1 p2 then K1 :: kx_merge r1 l2 else K2 :: go r2
end
end.
Definition kx_select (kx : kix) (rb : expr) (rk : Z) : list kentry :=
if is_lit0 rb then kx_merge (kx_bucket (kx_gran kx) (gran rk)) (kx_w0 kx)
else kx_wf kx.
Definition know_lookupA0I (bc : bctx) (kx : kix) (segs : list Segment) (rb : expr) (rk : Z)
(n : nat) (sx : bool) (hints : list bool) (acc : list sidecond) : lres :=
match hints, n with
| [], S _ => know_lookupA0B bc segs (kx_select kx rb rk) rb rk n sx [] acc
| _, _ => know_lookupA0B bc segs (kx_kn kx) rb rk n sx hints acc
end.
Lemma gran_div : ltac2:(TCodec.tc2 tcn__AxSymExec3BK ":'K'E&SAr1%211&\;+TP0%2241%73841pi091").
Proof. intros a. unfold gran. rewrite Z.shiftr_div_pow2 by lia. reflexivity. Qed.
Lemma gran_mono : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "='K&\<r2r1%3221&SAr3%211%316%8221p061pi:;1pi0<1").
Proof. intros a b H. rewrite !gran_div. apply Z.div_le_mono; lia. Qed.
Lemma gran_between : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "L'K&\<r3r1%3221&\=r2%2215'E'4&S9r5r4%3221(A%73621&S:r6&SA%117%43391%=3<17p071p0@1p0D1pQP<I1pj>J1pn:K1").
Proof.
intros s e x Hs He Hf. unfold ext_fits, ext_has in *.
destruct (Z.ltb s e); [|discriminate]. apply Z.leb_le in Hf.
pose proof (gran_mono s x Hs) as A. pose proof (gran_mono x (e - 1) ltac:(lia)) as B.
destruct (Z.eqb_spec (gran x) (gran s)); [reflexivity|].
destruct (Z.eqb_spec (gran x) (gran (e - 1))); [reflexivity|]. exfalso. lia.
Qed.
Lemma kx_aluop_eqb_refl : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "9'Q0'E'4&WCr1%2211(A%63521pi081"). Proof. intros []; reflexivity. Qed.
Lemma kx_mulop_eqb_refl : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "9'Q4'E'4&Z:r1%2211(A%63521pi081"). Proof. intros []; reflexivity. Qed.
Lemma kx_expr_eqb_refl : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "9'X<'E'4&X=r1%2211(A%63521pQP<81").
Proof.
induction x; cbn -[Z.eqb Nat.eqb]; rewrite ?kx_aluop_eqb_refl, ?kx_mulop_eqb_refl, ?IHx, ?IHx1, ?IHx2, ?Z.eqb_refl, ?Nat.eqb_refl, ?Bool.eqb_reflx; reflexivity.
Qed.
Lemma rel_lit_same : forall rb rk rn kk kl,
rel_lit rb rk rn rb kk kl =
if (Z.leb kk rk && Z.leb (rk + rn) (kk + kl))%bool then RInside (rk - kk)
else if (Z.leb (rk + rn) kk || Z.leb (kk + kl) rk)%bool then RDisjoint else RPartial.
Proof. intros. unfold rel_lit. rewrite kx_expr_eqb_refl. reflexivity. Qed.
Lemma rel_lit_other : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "J'X<'K'E'4&X=r6r3%3221(6%73621'ZD&ZIr7r5r4r2%564;32:1(W?%@3821p0:1pl8C1pl6D1pl4F1pn6F1pn4G1pn0I1").
Proof. intros rb rk rn kb kk kl H. unfold rel_lit. rewrite H. reflexivity. Qed.
Lemma is_lit0_eqb : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "A'X<'E'4&SKr1%211(A%63521&X=r3r2%3221%913%<3;21p071pl4?1pn0@1").
Proof.
intros rb kb H. destruct kb as [z| | | | | | |]; try discriminate. cbn in H.
destruct z; try discriminate.
destruct rb as [z'| | | | | | |]; cbn; try reflexivity; destruct z'; reflexivity.
Qed.
Lemma expr_eqb_lit0_l : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "='X<'E'4&X=(W<z%211r1%5221&SK%113%:3931pl4<1").
Proof. intros kb. destruct kb as [z| | | | | | |]; cbn; try reflexivity; destruct z; reflexivity. Qed.
Lemma is_lit0_true : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "?'X<'E'4&SKr1%211(A%63521r2(W<z%211%;3<41p061pj>>1").
Proof. intros e H. destruct e as [z| | | | | | |]; try discriminate. cbn in H. destruct z; try discriminate. reflexivity. Qed.
Lemma know_lookupA0B_skip0 : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "QA'R6'8'O%211'XO%411'K'9'4'ZO%911'E&T;&SAr4%211r6%5221(6%83;21'YL&T1r9r8(5r7%23F1:(W<z%211r5(1%11Br3(:%11Kr2%@9?>;875421%A9@?F986532%L3C21p0E1pi2O1po4Q21pm4Q41pn4Q61pn2Q81pQNQ:1pnHQ<1pi@Q@1").
Proof.
intros bc segs K rest rk n sx acc HC.
cbn [know_lookupA0B].
unfold kx_cand0, kx_wide0 in HC.
destruct K as [[kb kk] w v|[kb kk] len|[kb kk] len bk|lo hi|e m|e lo hi|a wn|a1 n1 a2 n2|[kb kk] len c|[kb kk] len];
cbn [lit0_extent] in HC; rewrite ?zmod64_eq in HC; try reflexivity.
-
destruct (is_lit0 kb) eqn:L.
+ apply is_lit0_true in L. subst kb. cbn [lit0_extent] in HC.
rewrite rel_lit_same.
destruct (Z.leb kk rk && Z.leb (rk + Z.of_nat (S n)) (kk + Z.of_nat w))%bool eqn:E.
* exfalso. apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2.
destruct (ext_fits kk (kk + Z.of_nat w)) eqn:F; [|discriminate].
rewrite (gran_between kk (kk + Z.of_nat w) rk) in HC; [discriminate|lia|lia|exact F].
* destruct (Z.leb (rk + Z.of_nat (S n)) kk || Z.leb (kk + Z.of_nat w) rk)%bool; reflexivity.
+ destruct kb as [z| | | | | | |]; try (rewrite rel_lit_other by reflexivity; reflexivity).
cbn in L. destruct z; try discriminate; rewrite rel_lit_other by reflexivity; reflexivity.
-
destruct (is_lit0 kb) eqn:L.
+ apply is_lit0_true in L. subst kb. destruct len as [l0| | | | | | |]; cbn [lit0_extent] in HC; rewrite ?zmod64_eq in HC; try discriminate.
rewrite rel_lit_same.
destruct (Z.leb kk rk && Z.leb (rk + Z.of_nat (S n)) (kk + l0 mod 2 ^ 64))%bool eqn:E.
* exfalso. apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2.
destruct (ext_fits kk (kk + l0 mod 2 ^ 64)) eqn:F; [|discriminate].
rewrite (gran_between kk (kk + l0 mod 2 ^ 64) rk) in HC; [discriminate|lia|lia|exact F].
* destruct (Z.leb (rk + Z.of_nat (S n)) kk || Z.leb (kk + l0 mod 2 ^ 64) rk)%bool; reflexivity.
+ destruct kb as [z| | | | | | |]; cbn [lit0_extent] in HC; try (destruct len; discriminate).
cbn in L. destruct z; try discriminate; destruct len; discriminate.
-
destruct (is_lit0 kb) eqn:L.
+ apply is_lit0_true in L. subst kb. destruct len as [l0| | | | | | |]; cbn [lit0_extent is_lit0] in HC; rewrite ?zmod64_eq in HC; try discriminate.
rewrite kx_expr_eqb_refl.
destruct (ext_fits kk (kk + l0 mod 2 ^ 64)) eqn:F; [|discriminate].
destruct (Z.leb_spec kk rk) as [H1|H1]; [|reflexivity].
destruct (Z.leb_spec (rk + Z.of_nat (S n)) (kk + (l0 mod 2 ^ 64))) as [H2|H2].
* exfalso. rewrite (gran_between kk (kk + l0 mod 2 ^ 64) rk) in HC; [discriminate|lia|lia|exact F].
* destruct (Z.leb_spec (kk + (l0 mod 2 ^ 64)) rk) as [H3|H3]; [reflexivity|].
exfalso. rewrite (gran_between kk (kk + l0 mod 2 ^ 64) rk) in HC; [discriminate|lia|lia|exact F].
+ rewrite expr_eqb_lit0_l, L. reflexivity.
-
destruct (ext_fits lo hi) eqn:F; [|discriminate].
destruct (Z.leb lo rk && Z.leb (rk + Z.of_nat (S n)) hi)%bool eqn:E; [|reflexivity].
exfalso. apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2.
rewrite (gran_between lo hi rk) in HC; [discriminate|lia|lia|exact F].
-
destruct (is_lit0 kb) eqn:L.
+ apply is_lit0_true in L. subst kb. destruct len as [l0| | | | | | |]; cbn [lit0_extent] in HC; rewrite ?zmod64_eq in HC; try discriminate.
cbv zeta. rewrite rel_lit_same.
destruct (Z.leb kk rk && Z.leb (rk + Z.of_nat (S n)) (kk + l0 mod 2 ^ 64))%bool eqn:E.
* exfalso. apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2.
destruct (ext_fits kk (kk + l0 mod 2 ^ 64)) eqn:F; [|discriminate].
rewrite (gran_between kk (kk + l0 mod 2 ^ 64) rk) in HC; [discriminate|lia|lia|exact F].
* destruct (Z.leb (rk + Z.of_nat (S n)) kk || Z.leb (kk + l0 mod 2 ^ 64) rk)%bool; reflexivity.
+ destruct kb as [z| | | | | | |]; cbn [lit0_extent] in HC; try (destruct len; discriminate).
cbn in L. destruct z; try discriminate; destruct len; discriminate.
Qed.
Lemma know_lookupA0B_skipf : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "QA'R6'8'O%211'XO%411'X<'K'9'4'ZO%:11'E&SKr5%211(6%53821&T<r8%211%93<15'YL&T1r;r:(5r9%23H19r7r6r4(:%11Hr3%<9;:765E421%=9<;A76F532%I3?21p0A1p0F1pi2M1po4Q01pm4Q21pn4Q41pn0Q61pn2Q81pQNQ:1pnHQ<1pi@Q@1").
Proof.
intros bc segs K rest rb rk n sx acc Hrb HC.
cbn [know_lookupA0B]. unfold kx_candf in HC.
destruct K as [[kb kk] w v|[kb kk] len|[kb kk] len bk|lo hi|e m|e lo hi|a wn|a1 n1 a2 n2|[kb kk] len c|[kb kk] len];
try reflexivity; try discriminate.
- destruct (is_lit0 kb) eqn:L; [|discriminate].
rewrite rel_lit_other; [reflexivity|]. rewrite (is_lit0_eqb rb kb L). exact Hrb.
- destruct (is_lit0 kb) eqn:L; [|discriminate].
rewrite (is_lit0_eqb rb kb L), Hrb. reflexivity.
- destruct rb as [z| | | | | | |]; try reflexivity. cbn in Hrb. destruct z; try reflexivity. discriminate.
Qed.
Lemma know_lookupA0B_filter0 : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "Q<'R6'8'O%211'XO%411'K'9'4'ZO%911'E'YL&T1r7r6&\4&T;&SAr4%211%411r5%73C21(W<z%211(1r3%211r2(:%11Hr1%E9DC;8?5421%F9ED=9@6532%I3H21pi2K1po4N1pm4Q01pn4Q21pl>Q41pnHQ71pi@Q;1").
Proof.
intros bc segs l rk n sx. induction l as [|K rest IH]; intros acc; [reflexivity|].
cbn [List.filter]. destruct (kx_cand0 (gran rk) K) eqn:HC.
-
cbn [know_lookupA0B]. rewrite !IH.
destruct K as [[kb kk] w v|[kb kk] len|[kb kk] len bk|lo hi|e m|e lo hi|a wn|a1 n1 a2 n2|[kb kk] len c|[kb kk] len]; try reflexivity.
- rewrite know_lookupA0B_skip0 by exact HC. apply IH.
Qed.
Lemma know_lookupA0B_filterf : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "Q<'R6'8'O%211'XO%411'X<'K'9'4'ZO%:11'E&SKr5%211(6%53821'YL&T1r9r8&\4&T<r7%33E21r6r4r3(:%11Er2%=9<;76B5421%>9=<97C6532%F3@21p0B1pi2I1po4L1pm4N1pn4Q01pn0Q21pl>Q41pnHQ71pi@Q;1").
Proof.
intros bc segs l rb rk n sx acc Hrb. revert acc. induction l as [|K rest IH]; intros acc; [reflexivity|].
cbn [List.filter]. destruct (kx_candf K) eqn:HC.
- cbn [know_lookupA0B]. rewrite !IH.
destruct K as [[kb kk] w v|[kb kk] len|[kb kk] len bk|lo hi|e m|e lo hi|a wn|a1 n1 a2 n2|[kb kk] len c|[kb kk] len]; try reflexivity.
- rewrite know_lookupA0B_skipf by assumption. apply IH.
Qed.
Fixpoint tagged (kn : list kentry) (i : positive) : list (positive * kentry) :=
match kn with [] => [] | K :: rest => (i, K) :: tagged rest (Pos.succ i) end.
Definition all_gt (i : positive) (l : list (positive * kentry)) : Prop := Forall (fun t => (i < fst t)%positive) l.
Lemma filter_tagged_gt : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "J'>'L'XO%3221'4p021'8%115&\8r1r2%3221&QK&\4r5&VNr4r3%3221%63@51%82:1p0:1pkJE1pk>F1pl:A1pR<D1").
Proof.
intros P kn. induction kn as [|K rest IH]; intros i j Hj; cbn [tagged List.filter]; [constructor|].
destruct (P (i, K)).
- constructor; [cbn; lia|]. apply IH. lia.
- apply IH. lia.
Qed.
Lemma kx_merge_nil_l : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "C'8'>'L'XO%3221%511'E%714&T>(:%116r1%4221&J&@%12=<%34<=15%;3:51plD=1").
Proof. reflexivity. Qed.
Lemma kx_merge_cons_l : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "M'L'XO'8'>%1243%311&QKr4r1%3221'E%91:&T>(5(=r5%24@?19r3%53>21r2%8221%9242%93E?1%=3<31p0?1plDD1pmLE1pQNJ1pmFL1").
Proof.
intros p K r1 l2 H. destruct l2 as [|[p2 K2] r2]; cbn [kx_merge].
- destruct r1 as [|[? ?] ?]; reflexivity.
- apply Forall_inv in H. cbn in H. destruct (Pos.ltb_spec p p2); [reflexivity|lia].
Qed.
Lemma kx_merge_cons_r : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "L'L'XO'8'>%1243%311&QKr4r2%3221'E%91:&T>r3(5(=r5%24A@1:%43>1:%7261%827<%73D>1%<3;31p0>1pmNC1plBD1pQNI1pmFK1").
Proof.
intros p K l1 r2 H. destruct l1 as [|[p1 K1] r1]; cbn [kx_merge List.map snd]; [reflexivity|].
apply Forall_inv in H. cbn in H. destruct (Pos.ltb_spec p1 p); [lia|reflexivity].
Qed.
Lemma kx_merge_filters : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "Q>'XO'4p021'8%114'L'Er5r1%211(A%53:21r2%611(6%93>21p051pQNA1&T>&\4'>%12@Er6&@%13CH@%311qo<51&VNr3%221A%;3941%H17qo<;1%>3<14%@241&<%>1L%221LqQNQ61%D3Q71;%Q23Q461p0H1pk>Q51pl:Q71pR>Q:1pR<Q;1").
Proof.
intros P Q kn. induction kn as [|K rest IH]; intros i HPQ; [reflexivity|].
cbn [tagged List.filter snd].
destruct (P K) eqn:HP.
- rewrite (HPQ K HP). cbn [orb]. rewrite kx_merge_cons_l; [rewrite IH; [reflexivity|exact HPQ]|].
apply filter_tagged_gt. lia.
- destruct (Q K) eqn:HQ; cbn [orb].
+ rewrite kx_merge_cons_r; [rewrite IH; [reflexivity|exact HPQ]|]. apply filter_tagged_gt. lia.
+ apply IH. exact HPQ.
Qed.
Definition narrow_in (g : Z) (K : kentry) : bool :=
match lit0_extent K with
| Some (s, e) => if ext_fits s e then ext_has s e g else false
| None => false
end.
Lemma kx_cand0_split : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "A'K'XO'E'4&T;r2r1%3221&<&UD%1254&T?%116%5231%<3;71pQN>1pjJ@1").
Proof.
intros g K. unfold kx_cand0, narrow_in, kx_wide0.
destruct (lit0_extent K) as [[s e]|]; [|reflexivity].
destruct (ext_fits s e); cbn [negb orb]; [rewrite Bool.orb_false_r|]; reflexivity.
Qed.
Lemma narrow_not_wide : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "A'K'XO'E'4&UDr2r1%3221(A%73621&T?%116(6%;3:21p051pQN>1pjJ@1").
Proof.
intros g K. unfold narrow_in, kx_wide0. destruct (lit0_extent K) as [[s e]|]; [|discriminate].
destruct (ext_fits s e); [reflexivity|discriminate].
Qed.
Lemma kx_gkey_inj : ltac2:(TCodec.tc2 tcn__AxSymExec3BK ">'K'E'L&T=r2%211r1%411%73631r3%93:16p031pi:<1pi0=1").
Proof. intros [|a|a] [|b|b] H; cbn in H; congruence. Qed.
Lemma kx_bucket_add_same : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "H'K'>'L'XO%3221'ZC'8%113%311'E&T9&T8r3r2r1%43321%6214(5%8246%23?61%;3=41po<=1pQP<B1pjJG1").
Proof. intros. unfold kx_add, kx_bucket at 1. rewrite pt_gss. reflexivity. Qed.
Lemma kx_bucket_add_other : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "L'K'>'L'XO%3221'ZC'8%113%311&G'Er4r3%33=21%511&T9&T8r2%23761r5%5221%6242%<3?21p091po<@1pQP<E1pjLJ1pjJK1").
Proof.
intros g g' x t H. unfold kx_add. unfold kx_bucket at 1. rewrite pt_gso; [reflexivity|].
intros E. apply H. apply kx_gkey_inj. exact E.
Qed.
Lemma kx_bucket_leaf : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "A'K'E'8'>'L'XO%3221%511&T9(W>%113r1%4221(:%118%>3831pjJ@1").
Proof. intros. unfold kx_bucket. rewrite pt_get_leaf. reflexivity. Qed.
Lemma kx_build_spec : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "QI'8'XO%211'L'>%1224%611'ZC%112'E%6242%7219&T:r5r4%3221(=r3r2%34=;21r1%54;C21%=3;71'D&\4&T?&@%13HJ7%311qo<H1&VNr6%221C%93L41%I3LD1'K&T9%12GA&UD%12E<qo<Q31r7%<21;%C3Q631%Q33Q671pjJ:1&T<%G3Q>1@%Q73Q>N1%J241%K2@1p0M1pQP4QB1pjNQ=1poLQ@1pk>QD1pl:QF1").
Proof.
induction kn as [|K rest IH]; intros i w0 gr wf H.
- cbn in H. injection H as <- <- <-. split; [reflexivity|]. split; [intros g; rewrite kx_bucket_leaf; reflexivity | reflexivity].
- cbn [kx_build] in H. destruct (kx_build rest (Pos.succ i)) as [[w0' gr'] wf'] eqn:Hb.
destruct (IH (Pos.succ i) w0' gr' wf' Hb) as (A & B & C). clear IH.
cbn [tagged List.filter snd].
assert (NW : forall g, narrow_in g K = match lit0_extent K with Some (s, e) => if ext_fits s e then ext_has s e g else false | None => false end) by reflexivity.
assert (WD : kx_wide0 K = match lit0_extent K with
| Some (s, e) => negb (ext_fits s e)
| None => match K with
| KZero (SA kb _) _ | KFill (SA kb _) _ _ => true
| KBlob (SA kb _) _ _ => is_lit0 kb
| _ => false
end
end) by reflexivity.
destruct (lit0_extent K) as [[s e]|] eqn:HE.
+ destruct (ext_fits s e) eqn:HF.
*
match type of H with (_, ?G, _) = _ => set (gr1 := G) in H end.
injection H as <- <- <-. rewrite WD. cbn [negb]. split; [exact A|]. split; [|rewrite C; reflexivity].
intros g. rewrite NW.
assert (STEP : kx_bucket gr1 g = if ext_has s e g then (i, K) :: kx_bucket gr' g else kx_bucket gr' g).
{ subst gr1. unfold ext_has. destruct (Z.eqb_spec (gran s) (gran (e - 1))) as [EQ|NE].
- destruct (Z.eqb_spec g (gran s)) as [->|NE1].
+ rewrite kx_bucket_add_same. reflexivity.
+ rewrite kx_bucket_add_other by exact NE1. destruct (Z.eqb_spec g (gran (e - 1))); [congruence|reflexivity].
- destruct (Z.eqb_spec g (gran s)) as [->|NE1].
+ rewrite kx_bucket_add_other by exact NE. rewrite kx_bucket_add_same. reflexivity.
+ destruct (Z.eqb_spec g (gran (e - 1))) as [->|NE2].
* rewrite kx_bucket_add_same. rewrite kx_bucket_add_other by exact NE1. reflexivity.
* rewrite kx_bucket_add_other by exact NE2. rewrite kx_bucket_add_other by exact NE1. reflexivity. }
rewrite STEP, B. reflexivity.
*
injection H as <- <- <-. rewrite WD. cbn [negb]. split; [rewrite A; reflexivity|]. split; [|rewrite C; reflexivity].
intros g. rewrite NW, B. reflexivity.
+ clear WD. destruct (kx_wide0 K); injection H as <- <- <-.
* split; [rewrite A; reflexivity|]. split; [|rewrite C; reflexivity]. intros g. rewrite NW, B. reflexivity.
* split; [exact A|]. split; [|rewrite C; reflexivity]. intros g. rewrite NW, B. reflexivity.
Qed.
Lemma kx_select_eq : forall kn rb rk,
kx_select (mk_kix kn) rb rk = if is_lit0 rb then List.filter (kx_cand0 (gran rk)) kn else List.filter kx_candf kn.
Proof.
intros kn rb rk. unfold kx_select, mk_kix.
destruct (kx_build kn 1%positive) as [[w0 gr] wf] eqn:Hb. cbn [kx_gran kx_w0 kx_wf fst snd].
destruct (kx_build_spec kn 1%positive w0 gr wf Hb) as (A & B & C).
destruct (is_lit0 rb); [|exact C].
rewrite B, A. rewrite (kx_merge_filters (narrow_in (gran rk)) kx_wide0 kn 1%positive (narrow_not_wide (gran rk))).
apply filter_ext. intros K. symmetry. apply kx_cand0_split.
Qed.
Theorem know_lookupA0I_eq : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "Q8'R6'8'XO%211'O%411'X<'K'9'4%911'ZO%;11'E'YL&T2r9&U>r8%211r7r6r5r4r3r2r1%<9;87654321&T1%19=9;876543%A3@31pi2C1pk<F1po4H1pm4J1pn4L1pn0N1pnHQ01pl:Q31pi@Q71").
Proof.
intros bc kn segs rb rk n sx hints acc. unfold know_lookupA0I.
destruct hints as [|h hs]; [|reflexivity]. destruct n as [|n]; [reflexivity|].
rewrite kx_select_eq. destruct (is_lit0 rb) eqn:L.
- apply is_lit0_true in L. subst rb. apply know_lookupA0B_filter0.
- apply know_lookupA0B_filterf. exact L.
Qed.
Definition know_lookupABI (bc : bctx) (kx : kix) (segs : list Segment) (kn : list kentry) (rb : expr) (rk : Z)
(n : nat) (sx : bool) (hints : list bool) (acc : list sidecond) : lres :=
match know_lookupA0I bc kx segs rb rk n sx hints acc with
| LMiss acc' hints' =>
match know_bytes_lit segs kn rb rk n with
| Some bs => LHit (lit_of_bytes sx n bs) acc' hints'
| None => LMiss acc' hints'
end
| r => r
end.
Lemma know_lookupABI_eq : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "Q2'R6'8'XO%211'O%411'E'X<'K'9'4%:11'ZO%<11'YLpi221pk<51po471pm491pn4;1pn0=1&T4r3&U>r2%211r1%645213&T3%13735%H3:31pnHJ1pl:M1pi@Q11").
Proof.
intros bc kn segs. bcfe. unfold know_lookupABI, know_lookupAB. rewrite know_lookupA0I_eq. reflexivity.
Qed.
Local Close Scope Z_scope.
Definition sym_readBI (segs : list Segment) (ss : sym_state) (bc : bctx) (kx : kix) (scr : scripts)
(a : saddr) (n : nat) (sx' : bool)
: option (expr * list sidecond * scripts * nat) :=
match log_lookupB bc (s_log ss) (a_base a) (a_off a) n sx' (sc_hints scr) [] with
| LStuck => None
| LHit v scs hints =>
Some (extKB bc v, flat_scB bc a n ++ scs, SCR (sc_dirs scr) (sc_reads scr) hints, s_next ss)
| LMiss scs hints =>
match know_lookupABI bc kx segs (s_know ss) (a_base a) (a_off a) n sx' hints scs with
| LStuck => None
| LHit v scs' hints' =>
Some (extKB bc v, flat_scB bc a n ++ scs', SCR (sc_dirs scr) (sc_reads scr) hints', s_next ss)
| LMiss scs' hints' =>
let i := s_next ss in
let rv := match sc_reads scr with [] => EVar i | e :: _ => e end in
let reads' := match sc_reads scr with [] => [] | _ :: t => t end in
Some (rv, flat_scB bc a n ++ SCReadBase a n sx' rv :: scs', SCR (sc_dirs scr) reads' hints', S i)
end
end.
Definition sym_stepBI (bc : bctx) (kx : kix) (segs : list Segment) (i : instr) (ss : sym_state) (scr : scripts) : stepres :=
let g r := sr_get (s_regs ss) r in
let p := s_pc ss in
match i with
| OpImm op rd rs imm => SOk (sset ss rd (mkAluKB bc op (g rs) (ELit (bv_signed imm))) (p + 4)) [] scr
| ShiftImm op rd rs sh => SOk (sset ss rd (mkAluKB bc op (g rs) (ELit (bv_unsigned sh))) (p + 4)) [] scr
| Op op rd rs1 rs2 => SOk (sset ss rd (mkAluKB bc op (g rs1) (g rs2)) (p + 4)) [] scr
| OpImm32 rd rs imm => SOk (sset ss rd (mkAluwKB bc ALU_ADD (g rs) (ELit (bv_signed imm))) (p + 4)) [] scr
| ShiftImm32 op rd rs sh => SOk (sset ss rd (mkAluw op (g rs) (ELit (bv_unsigned sh))) (p + 4)) [] scr
| Op32 op rd rs1 rs2 => SOk (sset ss rd (mkAluwKB bc op (g rs1) (g rs2)) (p + 4)) [] scr
| Mul op rd rs1 rs2 => SOk (sset ss rd (mkMdKB bc op (g rs1) (g rs2)) (p + 4)) [] scr
| Mul32 op rd rs1 rs2 => SOk (sset ss rd (mkMdw op (g rs1) (g rs2)) (p + 4)) [] scr
| Lui rd imm => SOk (sset ss rd (ELit (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_signed imm) 12)))) (p + 4)) [] scr
| Auipc rd imm => SOk (sset ss rd (ELit (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_signed imm) 12 + p)))) (p + 4)) [] scr
| Jal rd imm => SOk (sset ss rd (ELit (p + 4)) (bv_unsigned (Z_to_bv 64 (p + bv_signed imm)))) [] scr
| Jalr rd rs1 imm =>
match conc_exprB bc (g rs1) with
| ELit z => SOk (sset ss rd (ELit (p + 4)) (Z.land (bv_wrap 64 z + bv_signed imm) (-2) mod 2^64)) [] scr
| _ => SStop
end
| Branch c rs1 rs2 imm =>
let tk := bv_unsigned (Z_to_bv 64 (p + bv_signed imm)) in
let a := g rs1 in let b := g rs2 in
match match decide_branchB bc c a b with
| Some t => Some t
| None => match decide_branchB bc c (conc_exprB bc a) (conc_exprB bc b) with
| Some t => Some t
| None => enum_branchB bc c a b
end
end with
| Some t => SOk (sjump ss (if t then tk else p + 4)) [] scr
| None =>
match sc_dirs scr with
| [] => SStop
| t :: dirs' =>
SOk (sjump ss (if t then tk else p + 4)) [SCBr t c a b]
(SCR dirs' (sc_reads scr) (sc_hints scr))
end
end
| Fence _ _ _ _ _ => SOk (sjump ss (p + 4)) [] scr
| FenceI _ _ _ => SOk (sjump ss (p + 4)) [] scr
| Load sz sx rd rs imm =>
let n := msize_bytes sz in
let sx' := match sz with SZ8 => false | _ => sx end in
let a := to_saddrKB bc (g rs) (bv_signed imm) in
match sym_readBI segs ss bc kx scr a n sx' with
| None => SStop
| Some (v, scs, scr', nx') =>
SOk (SSR (p + 4) (if bv_eqb rd 0 then s_regs ss else sr_upd (s_regs ss) (ridx rd) v)
(s_log ss) (s_know ss) nx' (s_resv ss)) scs scr'
end
| Store sz rs1 rs2 imm =>
let n := msize_bytes sz in
let a := to_saddrKB bc (g rs1) (bv_signed imm) in
match resv_inval (s_resv ss) a with
| None => SStop
| Some r' =>
SOk (SSR (p + 4) (s_regs ss) (SE a n (g rs2) :: s_log ss) (s_know ss) (s_next ss) r')
(flat_scB bc a n ++ storeok_scB bc a n) scr
end
| Lr wd _ _ rd rs =>
let n := msize_bytes (amo_sz wd) in
let e := g rs in
if amo_alignedbB bc e wd then
let a := to_saddrKB bc e 0 in
match sym_readBI segs ss bc kx scr a n (amo_sx wd) with
| None => SStop
| Some (v, scs, scr', nx') =>
SOk (SSR (p + 4) (if bv_eqb rd 0 then s_regs ss else sr_upd (s_regs ss) (ridx rd) v)
(s_log ss) (s_know ss) nx' (Some a)) scs scr'
end
else SStop
| Sc wd _ _ rd rs1 rs2 =>
let n := msize_bytes (amo_sz wd) in
let e := g rs1 in
if amo_alignedbB bc e wd then
let a := to_saddrKB bc e 0 in
match s_resv ss with
| Some r =>
if saddr_eqb r a then
SOk (SSR (p + 4) (if bv_eqb rd 0 then s_regs ss else sr_upd (s_regs ss) (ridx rd) (ELit 0))
(SE a n (g rs2) :: s_log ss) (s_know ss) (s_next ss) None)
(flat_scB bc a n ++ storeok_scB bc a n) scr
else SStop
| None => SStop
end
else SStop
| Amo op wd _ _ rd rs1 rs2 =>
match amo_aluop op with
| None => SStop
| Some aop =>
let n := msize_bytes (amo_sz wd) in
let e := g rs1 in
if amo_alignedbB bc e wd then
let a := to_saddrKB bc e 0 in
match resv_inval (s_resv ss) a with
| None => SStop
| Some r' =>
match sym_readBI segs ss bc kx scr a n (amo_sx wd) with
| None => SStop
| Some (vold, scs, scr', nx') =>
SOk (SSR (p + 4) (if bv_eqb rd 0 then s_regs ss else sr_upd (s_regs ss) (ridx rd) vold)
(SE a n (amo_newvalB bc wd aop vold (g rs2)) :: s_log ss) (s_know ss) nx' r')
(scs ++ storeok_scB bc a n) scr'
end
end
else SStop
end
| _ => SStop
end.
Lemma sym_readBI_eqf : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "Q6'8'O%211'[>'R6'E'ZL'ZK'9'4';'>'X<'ZO%>11%4231%521:%6219%811po6:1pm4<1pi0>1pnB@1&VKr3r2r1&U>&ZJ%114%311%847651&VJ%13987%M3<31pi@O1pnNQ11pnHQ31").
Proof. intros. bcfe. unfold sym_readBI, sym_readB. rewrite know_lookupABI_eq. reflexivity. Qed.
Lemma sym_stepBI_eq : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "L'R6'8'O%211'Q3'[>'ZL'E'[3&VMr5&U>&ZJr2%211%411r4r3r1%:6943261&VL%15;5483%?3>31pnBA1pnNC1pk>E1pnHG1pi@K1").
Proof. intros. unfold sym_stepBI, sym_stepB. rewrite sym_readBI_eqf. reflexivity. Qed.
Lemma coeffs_divkB_eqf : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "E'8'XO%211'E'K'>'X<%2231%811'4poD21pm071&RA&UBr1%211%411&WL%114%@3831pjDB1").
Proof.
intros fk. apply functional_extensionality; intros m. apply functional_extensionality; intros ts.
induction ts as [|[k a] rest IH]; intros; bcfe; [reflexivity|].
cbn [coeffs_divkB coeffs_divk]. rewrite IH. (repeat first [ rewrite ealignB_eqf ]). reflexivity.
Qed.
#[export] Hint Rewrite coeffs_divkB_eqf : bceq.
Lemma lin_lowbits_knB_eqf : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "C'8'XO%211'E'X<'K';%112pkL31pj>51&TG&UBr1%211%411&YB%114%>3831pjD@1").
Proof. intros. bcfe. unfold lin_lowbits_knB, lin_lowbits_kn. (repeat first [ rewrite coeffs_divkB_eqf ]). reflexivity. Qed.
#[export] Hint Rewrite lin_lowbits_knB_eqf : bceq.
Lemma lin_nowrap_lB_eqf : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "E'8'XO%211'E'K'>'X<%2231%811'4poD21pj071&TJ&UBr1%211%411&YE%114%@3831pjDB1").
Proof. intros. bcfe. unfold lin_nowrap_lB, lin_nowrap_l. (repeat first [ rewrite erangeB_eqf ]). reflexivity. Qed.
#[export] Hint Rewrite lin_nowrap_lB_eqf : bceq.
Lemma mkSrlB_eqf : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "A'8'XO%211'E'X<'Kpn:12pi031&U;&UBr1%211%411&Z8%114%<3831pjD>1").
Proof. intros. bcfe. unfold mkSrlB, mkSrl. (repeat first [ rewrite erangeB_eqf | rewrite lin_nowrapB_eqf | rewrite lin_nowrap_lB_eqf ]). reflexivity. Qed.
#[export] Hint Rewrite mkSrlB_eqf : bceq.
Lemma lowbitsB_eqf : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "C'8'XO%211'E'X<'K';%112pkJ31pj>51&TO&UBr1%211%411&YK%114%>3831pjD@1").
Proof.
intros fk. apply functional_extensionality; intros e.
induction e; bcfe; cbn [lowbitsB lowbits]; rewrite ?IHe1, ?IHe2, ?IHe; (repeat first [ rewrite ealignB_eqf | rewrite lin_lowbits_knB_eqf ]); reflexivity.
Qed.
#[export] Hint Rewrite lowbitsB_eqf : bceq.
Lemma lsplit_divB_eqf : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "E'8'XO%211'E'K'>'X<%2231%811%4211poD21pm071&U0&UBr1%211%411&YM%114%@3831pjDB1").
Proof.
intros fk. apply functional_extensionality; intros m. apply functional_extensionality; intros ts.
induction ts as [|[k a] rest IH]; intros; bcfe; [reflexivity|].
cbn [lsplit_divB lsplit_div]. rewrite IH. (repeat first [ rewrite ealignB_eqf ]). reflexivity.
Qed.
#[export] Hint Rewrite lsplit_divB_eqf : bceq.
Lemma and_high_splitB_eqf : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "G'8'XO%211'E'X<'K'>%1223%811pn815pj<21pj061pkJ71piF91&QO&UBr1%211%411&WF%114%B3831pjDD1").
Proof. intros. bcfe. unfold and_high_splitB, and_high_split. (repeat first [ rewrite erangeB_eqf ]). reflexivity. Qed.
#[export] Hint Rewrite and_high_splitB_eqf : bceq.
Lemma and_low_splitB_eqf : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "F'8'XO%211'E'X<'K'>%1223%811pn815pj051pkJ61piF81&R0&UBr1%211%411&WG%114%A3831pjDC1").
Proof. intros. bcfe. unfold and_low_splitB, and_low_split. (repeat first [ rewrite erangeB_eqf ]). reflexivity. Qed.
#[export] Hint Rewrite and_low_splitB_eqf : bceq.
Lemma narrow_maskB_eqf : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "C'8'XO%211'E'X<'K';%112pkN31pi051&UE&UBr1%211%411&Z;%114%>3831pjD@1").
Proof. intros. bcfe. unfold narrow_maskB, narrow_mask. (repeat first [ rewrite xhiB_eqf ]). reflexivity. Qed.
#[export] Hint Rewrite narrow_maskB_eqf : bceq.
Lemma mkAnd0B_eqf : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "@'8'XO%211'E'X<pi:11pi021&U5&UBr1%211%411&Z3%114%;3831pjD=1").
Proof. intros. bcfe. unfold mkAnd0B, mkAnd0. (repeat first [ rewrite ealignB_eqf | rewrite coeffs_divkB_eqf | rewrite lin_lowbits_knB_eqf | rewrite mkSrlB_eqf | rewrite lowbitsB_eqf | rewrite lsplit_divB_eqf | rewrite and_high_splitB_eqf | rewrite and_low_splitB_eqf ]). reflexivity. Qed.
#[export] Hint Rewrite mkAnd0B_eqf : bceq.
Lemma mkAndB_eqf : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "@'8'XO%211'E'X<pi:11pi021&U6&UBr1%211%411&Z2%114%;3831pjD=1").
Proof. intros. bcfe. unfold mkAndB, mkAnd. (repeat first [ rewrite narrow_maskB_eqf | rewrite mkAnd0B_eqf ]). reflexivity. Qed.
#[export] Hint Rewrite mkAndB_eqf : bceq.
Lemma mkAndKB_eqf : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "@'8'XO%211'E'X<pi:11pi021&U7&UBr1%211%411&Z4%114%;3831pjD=1").
Proof. intros. bcfe. unfold mkAndKB, mkAndK. (repeat first [ rewrite mkAndB_eqf ]). reflexivity. Qed.
#[export] Hint Rewrite mkAndKB_eqf : bceq.
Lemma or_disjointB_eqf : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "A'8'XO%211'E'X<'4pi:21pi031&UM&UBr1%211%411&Z<%114%<3831pjD>1").
Proof. intros. bcfe. unfold or_disjointB, or_disjoint. (repeat first [ rewrite erangeB_eqf | rewrite ealignB_eqf ]). reflexivity. Qed.
#[export] Hint Rewrite or_disjointB_eqf : bceq.
Lemma mkOrB_eqf : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "@'8'XO%211'E'X<pi:11pi021&U9&UBr1%211%411&Z6%114%;3831pjD=1").
Proof. intros. bcfe. unfold mkOrB, mkOr. (repeat first [ rewrite mkAndKB_eqf | rewrite or_disjointB_eqf ]). reflexivity. Qed.
#[export] Hint Rewrite mkOrB_eqf : bceq.
Lemma conc_tryB_eqf : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "D'8'XO%211'E'X<%511';'K%211pj441pj>61&RC&UBr1%211%411&WN%114%?3831pjDA1").
Proof.
intros fk. apply functional_extensionality; intros e. apply functional_extensionality; intros cands.
induction cands as [|s rest IH]; intros; bcfe; [reflexivity|].
cbn [conc_tryB conc_try]. rewrite IH. (repeat first [ rewrite erangeB_eqf ]). reflexivity.
Qed.
#[export] Hint Rewrite conc_tryB_eqf : bceq.
Lemma concretizeB_eqf : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "B'8'XO%211'E'X<';'K%211pj>41&RD&UBr1%211%411&WO%114%=3831pjD?1").
Proof. intros. bcfe. unfold concretizeB, concretize. (repeat first [ rewrite conc_tryB_eqf ]). reflexivity. Qed.
#[export] Hint Rewrite concretizeB_eqf : bceq.
Lemma foldKB_eqf : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "?'8'XO%211'E'X<pj>11&S>&UBr1%211%411&XD%114%:3831pjD<1").
Proof. intros. bcfe. unfold foldKB, foldK. (repeat first [ rewrite erangeB_eqf | rewrite concretizeB_eqf ]). reflexivity. Qed.
#[export] Hint Rewrite foldKB_eqf : bceq.
Lemma lin_branchB_eqf : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "E'8'XO%211'E'Q2'X<';'4%211pi:41pi051pj071&TC&UBr1%211%411&Y>%114%@3831pjDB1").
Proof. intros. bcfe. unfold lin_branchB, lin_branch. (repeat first [ rewrite erangeB_eqf | rewrite lin_ge0B_eqf ]). reflexivity. Qed.
#[export] Hint Rewrite lin_branchB_eqf : bceq.
Lemma decide_branchB_eqf : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "E'8'XO%211'E'Q2'X<';'4%211pi:41pi051pj071&RE&UBr1%211%411&X0%114%@3831pjDB1").
Proof. intros. bcfe. unfold decide_branchB, decide_branch. (repeat first [ rewrite erangeB_eqf | rewrite lin_branchB_eqf ]). reflexivity. Qed.
#[export] Hint Rewrite decide_branchB_eqf : bceq.
Lemma mkSltB_eqf : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "D'8'XO%211'E'Q2'Q0'X<pi:11pi021pmD41pj061&U:&UBr1%211%411&Z7%114%?3831pjDA1").
Proof. intros. bcfe. unfold mkSltB, mkSlt. (repeat first [ rewrite decide_branchB_eqf ]). reflexivity. Qed.
#[export] Hint Rewrite mkSltB_eqf : bceq.
Lemma mkAluK0B_eqf : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "B'8'XO%211'E'Q0'X<pi:11pi021pmD41&U1&UBr1%211%411&YO%114%=3831pjD?1").
Proof. intros. bcfe. unfold mkAluK0B, mkAluK0. (repeat first [ rewrite mkSrlB_eqf | rewrite mkAndB_eqf | rewrite mkAndKB_eqf | rewrite mkOrB_eqf | rewrite mkSltB_eqf ]). reflexivity. Qed.
#[export] Hint Rewrite mkAluK0B_eqf : bceq.
Lemma mkAluKB_eqf : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "B'8'XO%211'E'Q0'X<pi:11pi021pmD41&U2&UBr1%211%411&YN%114%=3831pjD?1").
Proof. intros. bcfe. unfold mkAluKB, mkAluK. (repeat first [ rewrite foldKB_eqf | rewrite mkAluK0B_eqf ]). reflexivity. Qed.
#[export] Hint Rewrite mkAluKB_eqf : bceq.
Lemma mkMdKB_eqf : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "B'8'XO%211'E'Q4'X<pi:11pi021pmD41&U8&UBr1%211%411&Z5%114%=3831pjD?1").
Proof. intros. bcfe. unfold mkMdKB, mkMdK. (repeat first [ rewrite mkAluKB_eqf ]). reflexivity. Qed.
#[export] Hint Rewrite mkMdKB_eqf : bceq.
Lemma zband32B_eqf : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "@'8'XO%211'E'X<'4pj821&W;&UBr1%211%411&[O%114%;3831pjD=1").
Proof. intros. bcfe. unfold zband32B, zband32. (repeat first [ rewrite erangeB_eqf ]). reflexivity. Qed.
#[export] Hint Rewrite zband32B_eqf : bceq.
Lemma mkAluwK0B_eqf : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "B'8'XO%211'E'Q0'X<pi:11pi021pmD41&U3&UBr1%211%411&Z1%114%=3831pjD?1").
Proof. intros. bcfe. unfold mkAluwK0B, mkAluwK0. (repeat first [ rewrite erangeB_eqf | rewrite zband32B_eqf ]). reflexivity. Qed.
#[export] Hint Rewrite mkAluwK0B_eqf : bceq.
Lemma mkAluwKB_eqf : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "B'8'XO%211'E'Q0'X<pi:11pi021pmD41&U4&UBr1%211%411&Z0%114%=3831pjD?1").
Proof. intros. bcfe. unfold mkAluwKB, mkAluwK. (repeat first [ rewrite foldKB_eqf | rewrite mkAluwK0B_eqf ]). reflexivity. Qed.
#[export] Hint Rewrite mkAluwKB_eqf : bceq.
Lemma extK0B_eqf : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "?'8'XO%211'E'X<poF11&S7&UBr1%211%411&X?%114%:3831pjD<1").
Proof. intros. bcfe. unfold extK0B, extK0. (repeat first [ rewrite erangeB_eqf ]). reflexivity. Qed.
#[export] Hint Rewrite extK0B_eqf : bceq.
Lemma extKB_eqf : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "?'8'XO%211'E'X<poF11&S8&UBr1%211%411&X>%114%:3831pjD<1").
Proof. intros. bcfe. unfold extKB, extK. (repeat first [ rewrite foldKB_eqf | rewrite extK0B_eqf ]). reflexivity. Qed.
#[export] Hint Rewrite extKB_eqf : bceq.
Lemma flat_scB_eqf : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "C'8'XO%211'E'ZK'9'ZO%711pm431pi051&S=&UBr1%211%411&XC%114%>3831pjD@1").
Proof. intros. bcfe. unfold flat_scB, flat_sc. (repeat first [ rewrite base_rangeB_eqf ]). reflexivity. Qed.
#[export] Hint Rewrite flat_scB_eqf : bceq.
Lemma wr_coveredB_eqf : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "C'8'XO%211'E'ZK'9'4pm421pi041pl:71&W1&UBr1%211%411&[B%114%>3831pjD@1").
Proof.
intros fk. apply functional_extensionality; intros kn.
induction kn as [|K rest IH]; intros; bcfe; [reflexivity|].
cbn [wr_coveredB wr_covered]. rewrite IH. (repeat first [ rewrite xloB_eqf | rewrite xinsideB_eqf ]). reflexivity.
Qed.
#[export] Hint Rewrite wr_coveredB_eqf : bceq.
Lemma wr_coveredB_br_eqf : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "I'8'XO%211'E';'>'K%2211%411'ZK'9'4pm421pi041pl:<1piJ71&W2&UBr1%211%411&[C%114%D3831pjDF1").
Proof.
intros fk. apply functional_extensionality; intros br. apply functional_extensionality; intros kn.
induction kn as [|K rest IH]; intros; bcfe; [reflexivity|].
cbn [wr_coveredB_br wr_covered_br]. rewrite IH. (repeat first [ rewrite xloB_eqf | rewrite xinsideB_br_eqf ]). reflexivity.
Qed.
#[export] Hint Rewrite wr_coveredB_br_eqf : bceq.
Lemma storeok_scB_eqf : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "C'8'XO%211'E'ZK'9'ZO%711pm431pi051&V;&UBr1%211%411&[4%114%>3831pjD@1").
Proof. intros. bcfe. unfold storeok_scB, storeok_sc. (repeat first [ rewrite bc_fk_mkbc | rewrite base_rangeB_eqf | rewrite wr_coveredB_br_eqf ]). reflexivity. Qed.
#[export] Hint Rewrite storeok_scB_eqf : bceq.
Lemma conc_exprB_eqf : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "?'8'XO%211'E'X<pj>11&RB&UBr1%211%411&WM%114%:3831pjD<1").
Proof. intros. bcfe. unfold conc_exprB, conc_expr. (repeat first [ rewrite concretizeB_eqf ]). reflexivity. Qed.
#[export] Hint Rewrite conc_exprB_eqf : bceq.
Lemma enum_branchB_eqf : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "E'8'XO%211'E'Q2'X<';'4%211pi:41pi051pj071&S3&UBr1%211%411&X8%114%@3831pjDB1").
Proof. intros. bcfe. unfold enum_branchB, enum_branch. (repeat first [ rewrite concretizeB_eqf ]). reflexivity. Qed.
#[export] Hint Rewrite enum_branchB_eqf : bceq.
Lemma to_saddrKB_eqf : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "B'8'XO%211'E'X<'K'ZKpkF21pj>41&VO&UBr1%211%411&[A%114%=3831pjD?1").
Proof. intros. bcfe. unfold to_saddrKB, to_saddrK. (repeat first [ rewrite concretizeB_eqf ]). reflexivity. Qed.
#[export] Hint Rewrite to_saddrKB_eqf : bceq.
Lemma amo_alignedbB_eqf : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "B'8'XO%211'E'X<'Q1'4pQP221pj>41&QM&UBr1%211%411&WD%114%=3831pjD?1").
Proof. intros. bcfe. unfold amo_alignedbB, amo_alignedb. (repeat first [ rewrite lin_lowbits_knB_eqf ]). reflexivity. Qed.
#[export] Hint Rewrite amo_alignedbB_eqf : bceq.
Lemma amo_newvalB_eqf : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "F'8'XO%211'E'Q1';'Q0%211'X<pnL11pm@21pi641pQP281&QN&UBr1%211%411&WE%114%A3831pjDC1").
Proof. intros. bcfe. unfold amo_newvalB, amo_newval. (repeat first [ rewrite mkAluKB_eqf | rewrite mkAluwKB_eqf ]). reflexivity. Qed.
#[export] Hint Rewrite amo_newvalB_eqf : bceq.
Lemma log_lookupB_eqf : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "N'8'XO%211'E'ZM%511'X<'K'9'4%:11'ZO%<11'YLpi221pk<51po471pm491pn4;1pn0=1plN?1&TN&UBr1%211%411&YJ%114%I3831pjDK1").
Proof.
intros fk. apply functional_extensionality; intros log.
induction log as [|[[kb kk] w v] rest IH]; intros; bcfe; [reflexivity|].
cbn [log_lookupB log_lookup]. rewrite IH. (repeat first [ rewrite ranges_apartB_eqf ]). reflexivity.
Qed.
#[export] Hint Rewrite log_lookupB_eqf : bceq.
Lemma know_lookupA0B_eqf : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "O'8'XO%211'E'O%511'X<'K'9'4%:11'ZO%<11'YLpi221pk<51po471pm491pn4;1pn0=1pl:B1pnH@1&T1&UBr1%211%411&Y7%114%J3831pjDL1").
Proof.
intros fk. apply functional_extensionality; intros segs. apply functional_extensionality; intros kn.
induction kn as [|K rest IH]; intros; bcfe; [reflexivity|].
cbn [know_lookupA0B know_lookupA0]. rewrite IH. (repeat first [ rewrite erangeB_eqf | rewrite xinsideB_eqf ]). reflexivity.
Qed.
#[export] Hint Rewrite know_lookupA0B_eqf : bceq.
Lemma know_lookupAB_eqf : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "O'8'XO%211'E'O%511'X<'K'9'4%:11'ZO%<11'YLpi221pk<51po471pm491pn4;1pn0=1pl:B1pnH@1&T3&UBr1%211%411&Y6%114%J3831pjDL1").
Proof. intros. bcfe. unfold know_lookupAB, know_lookupA. (repeat first [ rewrite know_lookupA0B_eqf ]). reflexivity. Qed.
#[export] Hint Rewrite know_lookupAB_eqf : bceq.
Lemma sym_readB_eqf : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "Q5'8'XO%211'O%411'[>'E'ZL'ZK'9'4';'>'X<'ZO%?11%4231%521:%6219%811po6:1pm4<1pi0>1pnB@1&VJr2r1&UBr3%211%63541&[=%13764%K3:31pnNM1pnHO1pjDQ21").
Proof. intros. bcfe. unfold sym_readB, sym_read. (repeat first [ rewrite extKB_eqf | rewrite flat_scB_eqf | rewrite log_lookupB_eqf | rewrite know_lookupAB_eqf ]). reflexivity. Qed.
#[export] Hint Rewrite sym_readB_eqf : bceq.
Lemma know_lookupB_eqf : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "O'8'XO%211'O%411'E'X<'K'9'4%:11'ZO%<11'YLpi221pk<51po471pm491pn4;1pn0=1&T5r1&UBr2%211%5241&Y5%1264%G3931pnHI1pjDL1").
Proof. intros. bcfe. unfold know_lookupB, know_lookup. (repeat first [ rewrite bc_fk_mkbc | rewrite know_lookupAB_eqf ]). reflexivity. Qed.
#[export] Hint Rewrite know_lookupB_eqf : bceq.
Lemma sym_stepB_eq : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "K'8'O%211'Q3'[>'ZL'E'[3&VL&UB&XA&ZJr2%211%411%611r4r3r1%;543271&[?%145493%@3?31pnBB1pnND1pk>F1pnHH1").
Proof. intros. unfold sym_stepB, sym_step. (repeat first [ rewrite decide_branchB_eqf | rewrite mkAluKB_eqf | rewrite mkMdKB_eqf | rewrite mkAluwKB_eqf | rewrite flat_scB_eqf | rewrite storeok_scB_eqf | rewrite conc_exprB_eqf | rewrite enum_branchB_eqf | rewrite to_saddrKB_eqf | rewrite amo_alignedbB_eqf | rewrite amo_newvalB_eqf | rewrite sym_readB_eqf ]). reflexivity. Qed.
Lemma sym_step_know : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "Q4'8'O%211'Q3'[>'ZL'ZO%711'E'[3&[?r7r6r5r4%544321(W@r3r2r1%43321%=3<61'XO%G11&ZJ%11;%21>%C3421p071pnDH1pnFG1po0K1pnBK1pnNM1pk>O1pnHQ11").
Proof.
intros segs i ss scr ss' scs scr' H. unfold sym_step, sym_read in H.
destruct i; try discriminate;
repeat (lazymatch type of H with
| SOk _ _ _ = SOk _ _ _ => injection H as <- _ _
| (match ?x with _ => _ end) = _ => destruct x
| (let (_, _) := ?x in _) = _ => destruct x
| (if ?x then _ else _) = _ => destruct x
end); try discriminate; try reflexivity.
Qed.
Section WithSegs.
Variable segs : list Segment.
Definition zf_coversB (bc : bctx) (rb : expr) (rk : Z) (n : nat) (kb : expr) (kk : Z) (len : expr) : bool :=
(match len with
| ELit l0 => match rel_lit rb rk (Z.of_nat n) kb kk (l0 mod 2 ^ 64)%Z with RInside _ => true | _ => false end
| _ => false
end) || xinsideB bc rb rk (elen n) kb kk len.
Definition kentry_overlayB (bc : bctx) (rb : expr) (rk : Z) (n : nat) (K : kentry) : bool :=
match K with
| KUnk (SA kb kk) len | KZero (SA kb kk) len | KFill (SA kb kk) len _ | KBlob (SA kb kk) len _ =>
zf_coversB bc rb rk n kb kk len
| _ => false
end.
Definition kentry_readableB (bc : bctx) (rb : expr) (rk : Z) (n : nat) (K : kentry) : bool :=
match K with
| KWord (SA kb kk) w _ =>
match rel_lit rb rk (Z.of_nat n) kb kk (Z.of_nat w) with RInside _ => true | _ => false end
| _ => kentry_overlayB bc rb rk n K
end.
Definition kn_readableB (bc : bctx) (kn : list kentry) (rb : expr) (rk : Z) (n : nat) : bool :=
existsb (kentry_readableB bc rb rk n) kn || know_bytes_cov segs true kn rb rk n.
Definition kn_overlayB (bc : bctx) (kn : list kentry) (rb : expr) (rk : Z) (n : nat) : bool :=
existsb (kentry_overlayB bc rb rk n) kn || know_bytes_cov segs false kn rb rk n.
Definition x_dischargeableB (bc : bctx) (ss ss' : sym_state) (rb : option (saddr * nat * bool)) (sc : sidecond) : bool :=
let kn := s_know ss in
match sc with
| SCReadBase a n sx (EVar j) =>
(match rb with
| Some (a', n', sx') => saddr_eqb a' a && Nat.eqb n' n && Bool.eqb sx' sx
| None => false
end)
&& Nat.eqb j (s_next ss) && Nat.ltb j (s_next ss') && evars_lt (s_next ss) (a_base a)
&& Nat.leb 1 n && Nat.leb n 8 && kn_readable segs (bc_fk bc) kn (a_base a) (a_off a) n
| SCFlat a (ELit z) =>
Z.leb 1 z && Z.leb z 8 && kn_readable segs (bc_fk bc) kn (a_base a) (a_off a) (Z.to_nat z)
| SCStoreOk a n => Nat.leb 1 n && Nat.leb n 8 && kn_overlay segs (bc_fk bc) kn (a_base a) (a_off a) n
| _ => false
end%bool.
Definition x_filterB (bc : bctx) (ss ss' : sym_state) (scs : list sidecond) : list sidecond :=
match scs with
| [] => []
| _ => let rb := find_readbase (s_next ss) scs in
List.filter (fun sc => negb (x_dischargeableB bc ss ss' rb sc)) scs
end.
Definition sym_stepXB (bc : bctx) (K : nat) (i : instr) (ss : sym_state) (scr : scripts) : stepres :=
match sym_stepB bc segs i ss scr with
| SOk ss' scs scr' =>
if Nat.leb (s_next ss) (s_next ss')
then SOk (cap_rd K i ss') (x_filterB bc ss ss' scs) scr'
else SStop
| SStop => SStop
end.
Lemma zf_coversB_eqf : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "G'8'XO%211'E'X<'K'9'4plF41pl641pl461pm451pn471pn091&QJ&UBr1%211%411&\0%114%B3831pjDD1").
Proof. intros. bcfe. unfold zf_coversB, zf_covers. (repeat first [ rewrite xinsideB_eqf ]). reflexivity. Qed.
#[local] Hint Rewrite zf_coversB_eqf : bceq.
Lemma kentry_overlayB_eqf : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "E'8'XO%211'E'X<'K'9'4pQN71pm431pn451pn071&Q>&UBr1%211%411&Y0%114%@3831pjDB1").
Proof. intros. bcfe. unfold kentry_overlayB, kentry_overlay. (repeat first [ rewrite zf_coversB_eqf ]). reflexivity. Qed.
#[local] Hint Rewrite kentry_overlayB_eqf : bceq.
Lemma kentry_readableB_eqf : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "E'8'XO%211'E'X<'K'9'4pQN71pm431pn451pn071&Q?&UBr1%211%411&Y1%114%@3831pjDB1").
Proof. intros. bcfe. unfold kentry_readableB, kentry_readable. (repeat first [ rewrite kentry_overlayB_eqf ]). reflexivity. Qed.
#[local] Hint Rewrite kentry_readableB_eqf : bceq.
Lemma kn_readableB_eqf : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "F'8'XO%211'E'X<'K'9'4pm421pn441pn061pl:91&QA&UBr1%211%411&Y4v_;%2215%A3941pjDC1").
Proof. intros. bcfe. unfold kn_readableB, kn_readable. (repeat first [ rewrite kentry_readableB_eqf ]). reflexivity. Qed.
#[local] Hint Rewrite kn_readableB_eqf : bceq.
Lemma kn_overlayB_eqf : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "F'8'XO%211'E'X<'K'9'4pm421pn441pn061pl:91&Q@&UBr1%211%411&Y3v_;%2215%A3941pjDC1").
Proof. intros. bcfe. unfold kn_overlayB, kn_overlay. (repeat first [ rewrite kentry_overlayB_eqf ]). reflexivity. Qed.
#[local] Hint Rewrite kn_overlayB_eqf : bceq.
Lemma x_dischargeableB_eq : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "O'[>';'>'ZK'9%3221'4%5221%711'ZO'E&QH&UB&XA&ZJr4%211%411%611r3r2r1%;547321&[Dv_;%251:654%@3D41pn@B1pn0D1po0M1pnNN1").
Proof. intros. unfold x_dischargeableB, x_dischargeable. (repeat first [ rewrite bc_fk_mkbc ]). reflexivity. Qed.
Lemma x_filterB_eq : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "G'[>'8'ZO%211'E&QI&UB&XA&ZJr3%211%411%611r2r1%:43621&[Ev_;%241954%?3@41pnFA1po0E1pnNF1").
Proof.
intros. unfold x_filterB, x_filter. destruct scs as [|sc rest]; [reflexivity|].
erewrite filter_ext; [reflexivity|]. intros x. rewrite x_dischargeableB_eq. reflexivity.
Qed.
Lemma cap_rd_know : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "C'9'Q3'[>'E'8'XO%211&ZJ&WJr3r2r1%43321%611%713%<3921pnN>1pk>@1pQNB1").
Proof.
intros K i ss. unfold cap_rd. destruct K; [reflexivity|]. destruct (rd_of i) as [rd|]; [|reflexivity].
destruct (bv_eqb rd 0); [reflexivity|]. destruct (esize_le (sr_get (s_regs ss) rd) (S K)); reflexivity.
Qed.
Lemma sym_stepXB_eq : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "J'9'Q3'[>'ZL'E'[3&QF&UB&XA&ZJr2%211%411%611r4r3r1%;543271&[@v_;%25165:4%A3@41pnBC1pnNE1pk>G1pQNI1").
Proof.
intros. unfold sym_stepXB, sym_stepX. rewrite sym_stepB_eq.
destruct (sym_step segs i ss scr) as [ss' scs scr'|]; [|reflexivity]. rewrite x_filterB_eq. reflexivity.
Qed.
Lemma sym_stepX_know : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "Q4'9'Q3'[>'ZL'8'ZO%211'E'[3&[@v_;r7r6r5r4%6554321(W@r3r2r1%43321%>3=61'XO%C11&ZJ%11;%21>%D3421p071pnDJ1pnFH1po0M1pnBM1pnNO1pk>Q11pQNQ31").
Proof.
intros K i ss scr ss' scs scr' H. unfold sym_stepX in H.
destruct (sym_step segs i ss scr) as [ss1 scs1 scr1|] eqn:E; [|discriminate].
destruct (Nat.leb (s_next ss) (s_next ss1)); [|discriminate]. injection H as <- _ _.
rewrite cap_rd_know. exact (sym_step_know _ _ _ _ _ _ _ E).
Qed.
Fixpoint sym_execTXB_go (bc : bctx) (t : itab) (K : nat) (fuel : nat) (first : bool) (stops : list Z) (ss : sym_state) (ck : sym_state)
: sym_state :=
match fuel with
| O => if s_clean ss then ss else ck
| S f =>
if (negb first && existsb (Z.eqb (s_pc ss)) stops)%bool then (if s_clean ss then ss else ck) else
match itab_lookup t (s_pc ss) with
| None => if s_clean ss then ss else ck
| Some i =>
match sym_stepXB bc K i ss scr_nil with
| SOk ss' [] _ => sym_execTXB_go bc t K f false stops ss' (if s_clean ss' then ss' else ck)
| _ => if s_clean ss then ss else ck
end
end
end.
Definition sym_execTXB (bc : bctx) (t : itab) (K : nat) (fuel : nat) (first : bool) (stops : list Z) (ss : sym_state) : sym_state :=
sym_execTXB_go bc t K fuel first stops (clr ss) (clr ss).
Lemma sym_execTXB_go_eq : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "Q2&XJ'9'4'8'K%211'[>'E&QE&UB&XA&ZJr2%211%411%611r7r6r5r4r3r1%>8765432:1&[<v_;%28198765=4%C3D41pj6E1pnNF1po2H1pjBL1pjHN1pQNO1po<Q11").
Proof.
intros t K fuel. induction fuel as [|f IH]; intros first stops ss ck; [reflexivity|].
cbn [sym_execTXB_go sym_execTX_go].
destruct (negb first && existsb (Z.eqb (s_pc ss)) stops)%bool; [reflexivity|].
destruct (itab_lookup t (s_pc ss)) as [i|]; [|reflexivity].
rewrite sym_stepXB_eq. destruct (sym_stepX segs K i ss scr_nil) as [ss' scs scr'|] eqn:E; [|reflexivity].
destruct scs; [|reflexivity].
rewrite <- (sym_stepX_know _ _ _ _ _ _ _ E). apply IH.
Qed.
Lemma sym_execTXB_eq : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "Q7'8'XO%211&XJ'9'4'K%711'[>'E&ZJr1%211r7%53<21&QB&UB&XAr8%211%411r6r5r4r3r2%;76=54321&[;v_;%271@87654%E3F41p0A1pnNH1po2J1pjBM1pjHO1pQNQ01po<Q21pl<Q41").
Proof.
intros kn0 t K fuel first stops ss <-. unfold sym_execTXB, sym_execTX.
replace (s_know ss) with (s_know (clr ss)) by (destruct ss; reflexivity).
apply sym_execTXB_go_eq.
Qed.
Lemma sym_execTX_go_know : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "Q4&XJ'9'4'8'K%211'[>'E'XO%611&ZJr1%211r2%411%83631&[<v_;r8r7r6r5r4r3%887654321;%?11%@13%D3B21p0=1pj6G1pnNH1po2J1pjBN1pjHQ01pQNQ11po<Q31").
Proof.
intros t K fuel. induction fuel as [|f IH]; intros first stops ss ck Hck.
- cbn. destruct (s_clean ss); [reflexivity|exact Hck].
- cbn [sym_execTX_go].
destruct (negb first && existsb (Z.eqb (s_pc ss)) stops)%bool; [destruct (s_clean ss); [reflexivity|exact Hck]|].
destruct (itab_lookup t (s_pc ss)) as [i|]; [|destruct (s_clean ss); [reflexivity|exact Hck]].
destruct (sym_stepX segs K i ss scr_nil) as [ss' scs scr'|] eqn:E; [|destruct (s_clean ss); [reflexivity|exact Hck]].
destruct scs; [|destruct (s_clean ss); [reflexivity|exact Hck]].
pose proof (sym_stepX_know _ _ _ _ _ _ _ E) as HK.
rewrite IH; [exact HK|]. destruct (s_clean ss'); [reflexivity|]. rewrite Hck, HK. reflexivity.
Qed.
Lemma sym_execTX_know : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "M&XJ'9'4'8'K%211'[>'E'XO%611&ZJ&[;v_;r6r5r4r3r2r1%877654321%:11%;13%?3=21pnNA1po2C1pjBG1pjHI1pQNJ1po<L1").
Proof.
intros. unfold sym_execTX. rewrite sym_execTX_go_know; [|reflexivity]. destruct ss; reflexivity.
Qed.
Definition sym_stepXBI (bc : bctx) (kx : kix) (K : nat) (i : instr) (ss : sym_state) (scr : scripts) : stepres :=
match sym_stepBI bc kx segs i ss scr with
| SOk ss' scs scr' =>
if Nat.leb (s_next ss) (s_next ss')
then SOk (cap_rd K i ss') (x_filterB bc ss ss' scs) scr'
else SStop
| SStop => SStop
end.
Lemma sym_stepXBI_eq : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "L'9'Q3'[>'ZL'E'[3&QG&UB&XA&ZJr2%211%411%611&U>%114r4r3r1%=6643291&[@v_;%25165<4%C3B41pnBE1pnNG1pk>I1pQNK1").
Proof.
intros. unfold sym_stepXBI. rewrite sym_stepBI_eq. fold (sym_stepXB (mkbc (facts_of (s_know ss))) K i ss scr). apply sym_stepXB_eq.
Qed.
Fixpoint sym_execTXBI_go (bc : bctx) (kx : kix) (t : itab) (K : nat) (fuel : nat) (first : bool) (stops : list Z) (ss : sym_state) (ck : sym_state)
: sym_state :=
match fuel with
| O => if s_clean ss then ss else ck
| S f =>
if (negb first && existsb (Z.eqb (s_pc ss)) stops)%bool then (if s_clean ss then ss else ck) else
match itab_lookup t (s_pc ss) with
| None => if s_clean ss then ss else ck
| Some i =>
match sym_stepXBI bc kx K i ss scr_nil with
| SOk ss' [] _ => sym_execTXBI_go bc kx t K f false stops ss' (if s_clean ss' then ss' else ck)
| _ => if s_clean ss then ss else ck
end
end
end.
Definition sym_execTXBI (bc : bctx) (kx : kix) (t : itab) (K : nat) (fuel : nat) (first : bool) (stops : list Z) (ss : sym_state) : sym_state :=
sym_execTXBI_go bc kx t K fuel first stops (clr ss) (clr ss).
Lemma sym_execTXBI_go_eq : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "Q4&XJ'9'4'8'K%211'[>'E&QD&UB&XA&ZJr2%211%411%611&U>%114r7r6r5r4r3r1%@99765432<1&[<v_;%28198765?4%E3F41pj6G1pnNH1po2J1pjBN1pjHQ01pQNQ11po<Q31").
Proof.
intros t K fuel. induction fuel as [|f IH]; intros first stops ss ck; [reflexivity|].
cbn [sym_execTXBI_go sym_execTX_go].
destruct (negb first && existsb (Z.eqb (s_pc ss)) stops)%bool; [reflexivity|].
destruct (itab_lookup t (s_pc ss)) as [i|]; [|reflexivity].
rewrite sym_stepXBI_eq. destruct (sym_stepX segs K i ss scr_nil) as [ss' scs scr'|] eqn:E; [|reflexivity].
destruct scs; [|reflexivity].
rewrite <- (sym_stepX_know _ _ _ _ _ _ _ E). apply IH.
Qed.
Lemma sym_execTXBI_eq : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "Q9'8'XO%211&XJ'9'4'K%711'[>'E&ZJr1%211r7%53<21&QC&UB&XAr8%211%411&U>%114r6r5r4r3r2%=886?54321&[;v_;%271B87654%G3H41p0C1pnNJ1po2L1pjBO1pjHQ11pQNQ21po<Q41pl<Q61").
Proof.
intros kn0 t K fuel first stops ss <-. unfold sym_execTXBI, sym_execTX.
replace (s_know ss) with (s_know (clr ss)) by (destruct ss; reflexivity).
apply sym_execTXBI_go_eq.
Qed.
End WithSegs.
Definition kcutB (bc : bctx) (mk : saddr -> expr -> kentry) (wb : expr) (wk : Z) (wn : expr)
(kb : expr) (kk : Z) (len : expr) : list kentry :=
let ws := mkAlu ALU_ADD wb (ELit wk) in
let ks := mkAlu ALU_ADD kb (ELit kk) in
let low :=
if (if lin_ge0B bc [(kb, kk)] [(wb, wk)] then false
else if lin_ge0B bc [(wb, wk)] [(kb, kk)] then lin_ge0B bc [(kb, kk); (len, 0%Z)] [(wb, wk)] else false)
then [mk (SA kb kk) (mkAlu ALU_SUB ws ks)] else [] in
let high :=
if (if lin_ge0B bc [(kb, kk); (len, 0%Z)] [(wb, wk); (wn, 0%Z)]
then if lin_ge0B bc [(wb, wk); (wn, 0%Z)] [(kb, kk)]
then lin_ge0B bc [(ELit 0, (two64 - 1)%Z)] [(kb, kk); (len, 0%Z)]
else false
else false)
then let we := mkAlu ALU_ADD ws wn in
let '(hb, ho) := split_lit we in
let ha := if (lin_ge0B bc [(hb, ho)] [(wb, wk); (wn, 0%Z)] && lin_ge0B bc [(wb, wk); (wn, 0%Z)] [(hb, ho)])%bool
then SA hb ho else SA we 0%Z in
[mk ha (mkAlu ALU_SUB (mkAlu ALU_ADD ks len) we)]
else [] in
low ++ high.
Definition kzero_cutB (bc : bctx) (wb : expr) (wk : Z) (wn : expr)
(kb : expr) (kk : Z) (len : expr) : list kentry := kcutB bc KZero wb wk wn kb kk len.
Definition kfill_cutB (bc : bctx) (c : Z) (wb : expr) (wk : Z) (wn : expr)
(kb : expr) (kk : Z) (len : expr) : list kentry := kcutB bc (fun a n => KFill a n c) wb wk wn kb kk len.
Definition kunk_cutB (bc : bctx) (wb : expr) (wk : Z) (wn : expr)
(kb : expr) (kk : Z) (len : expr) : list kentry := kcutB bc KUnk wb wk wn kb kk len.
Definition prune_zfB (bc : bctx) (mk : saddr -> expr -> kentry) (wb : expr) (k : Z) (w : nat)
(K : kentry) (kb : expr) (kk : Z) (len : expr) (apart : unit -> bool) (hints : list bool)
(diffbase : unit -> list kentry * list sidecond * list bool)
: list kentry * list sidecond * list bool :=
if expr_eqb kb wb then
match len with
| ELit l0 => (ktrim mk kb kk l0 k w, [], hints)
| _ => if Z.leb (k + Z.of_nat w) kk then ([K], [], hints)
else (kcutB bc mk wb k (elen w) kb kk len, [], hints)
end
else if apart tt then ([K], [], hints)
else match kcutB bc mk wb k (elen w) kb kk len with
| [] => diffbase tt
| cut => (cut, [], hints)
end.
Definition prune1pB (bc : bctx) (sp : sprep) (wa : saddr) (w : nat) (wv : expr) (K : kentry) (hints : list bool)
: list kentry * list sidecond * list bool :=
let k := a_off wa in
let diffbase (ka : saddr) (kl : expr) :=
let apart := ranges_apart_pB bc sp (a_base wa) k (elen w) (a_base ka) (a_off ka) kl in
if apart then ([K], [], hints) else
match hints with
| true :: hs => ([K], [SCDisj wa (elen w) ka kl], hs)
| false :: hs => ([], [], hs)
| [] => ([], [], [])
end in
match K with
| KAlign _ _ => ([K], [], hints)
| KRange _ _ _ => ([K], [], hints)
| KWr _ _ => ([K], [], hints)
| KDisj _ _ _ _ => ([K], [], hints)
| KImg lo hi =>
match a_base wa with
| ELit 0 =>
let r1 := if Z.ltb lo (Z.min k hi) then [KImg lo (Z.min k hi)] else [] in
let lo2 := Z.max lo (k + Z.of_nat w) in
let r2 := if Z.ltb lo2 hi then [KImg lo2 hi] else [] in
(r1 ++ r2, [], hints)
| _ => if Z.ltb (hi - lo) (2 ^ 64) then diffbase (SA (ELit 0) lo) (ELit (hi - lo))
else ([], [], hints)
end
| KZero (SA kb kk) len =>
prune_zfB bc KZero (a_base wa) k w K kb kk len
(fun _ => ranges_apart_pB bc sp (a_base wa) k (elen w) kb kk len) hints (fun _ => diffbase (SA kb kk) len)
| KFill (SA kb kk) len c =>
prune_zfB bc (fun a n => KFill a n c) (a_base wa) k w K kb kk len
(fun _ => ranges_apart_pB bc sp (a_base wa) k (elen w) kb kk len) hints (fun _ => diffbase (SA kb kk) len)
| KUnk (SA kb kk) len =>
prune_zfB bc KUnk (a_base wa) k w K kb kk len
(fun _ => ranges_apart_pB bc sp (a_base wa) k (elen w) kb kk len) hints (fun _ => diffbase (SA kb kk) len)
| KWord (SA kb kk) w' v =>
if expr_eqb kb (a_base wa) then
(if (Z.leb (kk + Z.of_nat w') k || Z.leb (k + Z.of_nat w) kk)%bool
then ([K], [], hints) else (kword_cut kb kk w' v k w, [], hints))
else if ranges_apart_pB bc sp (a_base wa) k (elen w) kb kk (elen w') then ([K], [], hints)
else if (Nat.eqb w 1 && Nat.eqb w' 1 && expr_eqb wv v)%bool
then ([K], [], hints)
else diffbase (SA kb kk) (elen w')
| KBlob (SA kb kk) len bk =>
if expr_eqb kb (a_base wa) then
match len with
| ELit l0 =>
let l := (l0 mod 2 ^ 64)%Z in
(if (Z.leb (kk + l) k || Z.leb (k + Z.of_nat w) kk)%bool
then ([K], [], hints) else ([], [], hints))
| _ => if Z.leb (k + Z.of_nat w) kk then ([K], [], hints) else ([], [], hints)
end
else diffbase (SA kb kk) len
end.
Definition ranges_apart_pcB (bc : bctx) (sp : sprep) (b1 : expr) (k1 : Z) (n1 : expr)
(br2 : option (Z * Z)) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
match n1, n2 with
| ELit z1, ELit z2 =>
let m1 := zlit64 z1 in let m2 := zlit64 z2 in
if expr_eqb b2 b1 then (Z.leb (k1 + m1) k2 || Z.leb (k2 + m2) k1)%bool else
if (match sp_rng sp, br2 with
| Some (lo1, hi1), Some (lo2, hi2) =>
(Z.leb (hi1 + k1 + m1) (lo2 + k2) || Z.leb (hi2 + k2 + m2) (lo1 + k1))%bool
| _, _ => false
end) then true
else if in_sidesB_br bc br2 (sp_D sp) b2 k2 m2 then true
else lin_apartB bc b1 k1 m1 b2 k2 m2
| _, _ =>
if (match sp_rng sp, br2, sp_h1 sp, xhiB bc n2 with
| Some (lo1, hi1), Some (lo2, hi2), Some h1, Some h2 =>
if (Z.leb (hi1 + k1 + h1) (lo2 + k2) || Z.leb (hi2 + k2 + h2) (lo1 + k1))%bool then true
else
if match end_hiB bc b1 k1 n1 lo1 hi1 h1 with Some e1 => Z.leb e1 (lo2 + k2) | None => false end then true
else match end_hiB bc b2 k2 n2 lo2 hi2 h2 with Some e2 => Z.leb e2 (lo1 + k1) | None => false end
| _, _, _, _ => false
end) then true
else if in_sides_xB_br bc br2 (sp_Dx sp) b2 k2 n2 then true
else if negb (shares_var b1 b2) then false
else if lin_ge0B bc [(b2, k2)] [(b1, k1); (n1, 0%Z)] then true
else lin_ge0B bc [(b1, k1)] [(b2, k2); (n2, 0%Z)]
end.
Definition prune1pcB (bc : bctx) (sp : sprep) (wa : saddr) (w : nat) (wv : expr) (K : kentry) (hints : list bool)
(br2 : option (Z * Z)) : list kentry * list sidecond * list bool :=
let k := a_off wa in
let diffbase (ka : saddr) (kl : expr) :=
let apart := ranges_apart_pcB bc sp (a_base wa) k (elen w) br2 (a_base ka) (a_off ka) kl in
if apart then ([K], [], hints) else
match hints with
| true :: hs => ([K], [SCDisj wa (elen w) ka kl], hs)
| false :: hs => ([], [], hs)
| [] => ([], [], [])
end in
match K with
| KAlign _ _ | KRange _ _ _ | KWr _ _ | KDisj _ _ _ _ | KImg _ _ => prune1pB bc sp wa w wv K hints
| KZero (SA kb kk) len =>
if expr_eqb kb (a_base wa) then prune1pB bc sp wa w wv K hints
else if ranges_apart_pcB bc sp (a_base wa) k (elen w) br2 kb kk len then ([K], [], hints)
else match kzero_cutB bc (a_base wa) k (elen w) kb kk len with
| [] => diffbase (SA kb kk) len
| cut => (cut, [], hints)
end
| KFill (SA kb kk) len c =>
if expr_eqb kb (a_base wa) then prune1pB bc sp wa w wv K hints
else if ranges_apart_pcB bc sp (a_base wa) k (elen w) br2 kb kk len then ([K], [], hints)
else match kfill_cutB bc c (a_base wa) k (elen w) kb kk len with
| [] => diffbase (SA kb kk) len
| cut => (cut, [], hints)
end
| KUnk (SA kb kk) len =>
if expr_eqb kb (a_base wa) then prune1pB bc sp wa w wv K hints
else if ranges_apart_pcB bc sp (a_base wa) k (elen w) br2 kb kk len then ([K], [], hints)
else match kunk_cutB bc (a_base wa) k (elen w) kb kk len with
| [] => diffbase (SA kb kk) len
| cut => (cut, [], hints)
end
| KWord (SA kb kk) w' v =>
if expr_eqb kb (a_base wa) then prune1pB bc sp wa w wv K hints
else if ranges_apart_pcB bc sp (a_base wa) k (elen w) br2 kb kk (elen w') then ([K], [], hints)
else if (Nat.eqb w 1 && Nat.eqb w' 1 && expr_eqb wv v)%bool
then ([K], [], hints)
else diffbase (SA kb kk) (elen w')
| KBlob (SA kb kk) len bk =>
if expr_eqb kb (a_base wa) then prune1pB bc sp wa w wv K hints
else diffbase (SA kb kk) len
end.
Fixpoint prunepcB (bc : bctx) (sp : sprep) (wa : saddr) (w : nat) (wv : expr) (kn : list kentry) (hints : list bool)
(cache : list (expr * option (Z * Z))) : list kentry * list sidecond * list bool :=
match kn with
| [] => ([], [], hints)
| K :: rest =>
let '(br2, cache') :=
match kbase K with
| Some kb => match br_lookup cache kb with
| Some r => (r, cache)
| None => let r := base_rangeB bc kb in (r, (kb, r) :: cache)
end
| None => (None, cache)
end in
let '(kept, scs1, hs1) := prune1pcB bc sp wa w wv K hints br2 in
let '(r, scs2, hs2) := prunepcB bc sp wa w wv rest hs1 cache' in
(kept ++ r, scs1 ++ scs2, hs2)
end.
Lemma kcutB_eqf : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "K'8'XO%211'E'ZK'X<p015p031'KplF47pl621pl461pQP871pQP651pQP091pm281&SL&UBr1%211%411&XLr2%2251qm2A1%F3:51pjDH1").
Proof. intros. bcfe. unfold kcutB, kcut. (repeat first [ rewrite lin_ge0B_eqf ]). reflexivity. Qed.
#[export] Hint Rewrite kcutB_eqf : bceq.
Lemma kzero_cutB_eqf : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "E'8'XO%211'E'X<'KplF24pl621pl441pQP851pQP651pQP071&T@&UBr1%211%411&Y;%114%@3831pjDB1").
Proof. intros. bcfe. unfold kzero_cutB, kzero_cut. (repeat first [ rewrite kcutB_eqf ]). reflexivity. Qed.
#[export] Hint Rewrite kzero_cutB_eqf : bceq.
Lemma kfill_cutB_eqf : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "H'8'XO%211'E'K'X<plF14pl631pl431pQP841pQP661pQP061pj081&T0&UBr1%211%411&Y2r2%2251qj0A1%C3:51pjDE1").
Proof. intros. bcfe. unfold kfill_cutB, kfill_cut. (repeat first [ rewrite kcutB_eqf ]). reflexivity. Qed.
#[export] Hint Rewrite kfill_cutB_eqf : bceq.
Lemma kunk_cutB_eqf : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "E'8'XO%211'E'X<'KplF24pl621pl441pQP851pQP651pQP071&T6&UBr1%211%411&Y9%114%@3831pjDB1").
Proof. intros. bcfe. unfold kunk_cutB, kunk_cut. (repeat first [ rewrite kcutB_eqf ]). reflexivity. Qed.
#[export] Hint Rewrite kunk_cutB_eqf : bceq.
Lemma prune_zfB_eqf : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "Q:'8'XO%211'E'ZK'X<p015p031'K'9'C'4p021%=12'>'ZO%@11%32?1%4215p091pj:12pk<81pi8:1plFB1pl6@1pl4D1pQNI1poHB1pkLD1pQP0H1pm2G1&V3&UBr1%211%411&Z?r2%2251qm2Q01%Q53:51pjDQ71").
Proof. intros. bcfe. unfold prune_zfB, prune_zf. (repeat first [ rewrite kcutB_eqf ]). reflexivity. Qed.
#[export] Hint Rewrite prune_zfB_eqf : bceq.
Lemma prune1pB_eqf : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "N'8'XO%211'E'[1'ZK'9'X<'4%911'>'ZO%<11%32;1%4215pk<61pQN?1pQP::1poH<1poN>1pnJ@1&V0&UBr1%211%411&Z=%114%I3831pjDK1").
Proof. intros. bcfe. unfold prune1pB, prune1p. (repeat first [ rewrite ranges_apart_pB_eqf | rewrite prune_zfB_eqf ]). reflexivity. Qed.
#[export] Hint Rewrite prune1pB_eqf : bceq.
Lemma ranges_apart_pcB_eqf : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "M'8'XO%211'E'[1'X<'K';'>%1233%311'4pm871pl271pi>91piN51pm6;1pl0;1pi<=1pnJ?1&V7&UBr1%211%411&ZG%114%H3831pjDJ1").
Proof. intros. bcfe. unfold ranges_apart_pcB, ranges_apart_pc. (repeat first [ rewrite lin_apartB_eqf | rewrite xhiB_eqf | rewrite lin_ge0B_eqf | rewrite end_hiB_eqf | rewrite in_sidesB_br_eqf | rewrite in_sides_xB_br_eqf ]). reflexivity. Qed.
#[export] Hint Rewrite ranges_apart_pcB_eqf : bceq.
Lemma prune1pcB_eqf : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "Q3'8'XO%211'E'[1'ZK'9'X<'4%911';'>'K%2211%411'ZO%@11%62?1%7219piN51pk<;1pQND1pQP:?1poHA1poNC1pnJE1&V1&UBr1%211%411&Z>%114%N3831pjDQ01").
Proof. intros. bcfe. unfold prune1pcB, prune1pc. (repeat first [ rewrite kzero_cutB_eqf | rewrite kfill_cutB_eqf | rewrite kunk_cutB_eqf | rewrite prune1pB_eqf | rewrite ranges_apart_pcB_eqf ]). reflexivity. Qed.
#[export] Hint Rewrite prune1pcB_eqf : bceq.
Lemma prunepcB_eqf : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "Q5'8'XO%211'E'[1'ZK'9'X<'4%911'>';'K%3211%311%5281%@11'ZO%B11%92A1%:21;pj251pk<=1pl:E1pQP:A1poHC1poNE1pnJG1&V4&UBr1%211%411&ZA%114%Q03831pjDQ21").
Proof.
intros fk. apply functional_extensionality; intros sp. apply functional_extensionality; intros wa. apply functional_extensionality; intros w. apply functional_extensionality; intros wv. apply functional_extensionality; intros kn.
induction kn as [|K rest IH]; intros; bcfe; [reflexivity|].
cbn [prunepcB prunepc]. rewrite IH. (repeat first [ rewrite base_rangeB_eqf | rewrite prune1pcB_eqf ]). reflexivity.
Qed.
#[export] Hint Rewrite prunepcB_eqf : bceq.
#[export] Hint Rewrite zf_coversB_eqf kentry_overlayB_eqf kentry_readableB_eqf kn_readableB_eqf kn_overlayB_eqf : bceq.
Lemma filter_nil_app : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "E'8'XO%211'E&\4&XIr2%33621(:%118%73831&3r4r3%33=21%;3>:1%=3>17p071p081plDA1plBB1").
Proof. intros l1 l2 H1 H2. rewrite List.filter_app, H1, H2. reflexivity. Qed.
Lemma filter_if_single : forall (c : bool) K,
is_factb K = false -> List.filter is_factb (if c then [K] else []) = [].
Proof. intros c K H. destruct c; cbn; rewrite ?H; reflexivity. Qed.
Lemma kcut_nofacts : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "Q;'ZK'X<'XOpQP>21pQP<41'8%114'K'E'4&XIr:r2r1%3221%511(6%93821pm4A1pi0C1&\4&XLr9r8r7r6r5r4r3%887654321A%:3LD1(:%11N%I3K31p0?1plFQ21pl6M1pl4Q41pQP8Q51pQP6Q01pQP0Q71pl:Q31pm2Q61").
Proof.
intros mk kn wb wk wn kb kk len H. unfold kcut.
apply filter_nil_app.
- apply filter_if_single. apply H.
- match goal with |- List.filter is_factb (if ?c then _ else _) = [] => destruct c; [|reflexivity] end.
destruct (split_lit (mkAlu ALU_ADD (mkAlu ALU_ADD wb (ELit wk)) wn)) as [hb ho].
cbn [List.filter]. rewrite H. reflexivity.
Qed.
Lemma ktrim_nofacts : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "Q8'ZK'X<'XOpQP>21pQP<41'K'9'E'4&XIr8r2r1%3221%511(6%93821pm4@1pi0B1'8%11B&\4&Y8r7r6r5r4r3%6654321A%83KD1(:%11M%I3<31p0?1poHL1pkLN1pl@O1pl6Q01pl4Q51pm2Q31").
Proof. intros. unfold ktrim. apply filter_nil_app; apply filter_if_single; apply H. Qed.
Lemma kword_cut_nofacts : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "K'X<'K'9'E'8'XO%211&\4&XI&Y:r6r5r4r3r2r1%76654321%:3<91(:%11>%A3>31poHC1pkLE1poFG1poJF1pl6H1pl4J1").
Proof.
intros. unfold kword_cut. destruct v; try reflexivity.
apply filter_nil_app; apply filter_if_single; reflexivity.
Qed.
Lemma prune_zf_nofacts : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "R;'ZK'X<'XOpQP>21pQP<41'8%114'K'9'C'4p021%712'>'ZO%:11%32:1%4215pQP<91'E&XIr>r2r1%3221%511(6%83A21pm4K1pi0M1r8%;11%=3F16&\4&7r3(B%211%43FJ1%53Q1H1%73Q6D1(:%11Q8%H3Q531&Z?r?r=r<r;r:r9r7r6r5r4%;<:Q298765I4321%F3Q8Q<1%G3QCQ:1%I3QHQ61%Q83QE1Ap0A1p0M1p0Q11pj:Q=1pk<QD1pi8QF1plFR11pl6QL1pl4R31pQNR31poHQN1pkLR01pQP0R71pi4R31pm2R61").
Proof.
intros mk allkn wb k w K kb kk len apart hints diffbase Hm HK Hd. unfold prune_zf.
destruct (expr_eqb kb wb).
- destruct len; cbn [fst]; try (apply ktrim_nofacts; exact Hm);
(destruct (Z.leb (k + Z.of_nat w) kk); cbn [fst List.filter]; [rewrite HK; reflexivity | apply kcut_nofacts; exact Hm]).
- destruct (apart tt); cbn [fst List.filter]; [rewrite HK; reflexivity|].
destruct (kcut mk allkn wb k (elen w) kb kk len) as [|c cs] eqn:E; [exact Hd|].
cbn [fst]. rewrite <- E. apply kcut_nofacts. exact Hm.
Qed.
Ltac nfcrush :=
cbn [fst List.filter is_factb];
first [ reflexivity
| apply kword_cut_nofacts
| (apply filter_nil_app; apply filter_if_single; reflexivity)
| match goal with
| |- context [if ?c then _ else _] => destruct c; nfcrush
| |- context [match ?h with nil => _ | cons _ _ => _ end] => destruct h; nfcrush
| |- context [match ?h with ELit _ => _ | _ => _ end] => destruct h; nfcrush
| |- context [match ?h with Z0 => _ | _ => _ end] => destruct h; nfcrush
end ].
Lemma prune1p_facts : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "Q:'8'XO%211'[1'ZK'9'X<'4%811'E&\4&XI&7'ZO%>11'>%12>2&Z=r7r6r5r4r3r2r1%877654321%>3:B1%?3I=1%B3KA1(5(:%11N%33O91%G3Q0F1%I3Q061pk<K1pQNQ31pQP:O1poHQ11poNQ31pnJQ51pi4Q71").
Proof.
intros allkn sp wa w wv K hints. unfold prune1p.
destruct K as [[kb kk] w' v|[kb kk] len|[kb kk] len bk|lo hi|e m|e lo hi|[kb kk] n|a1 n1 a2 n2|[kb kk] len c|[kb kk] len]; cbn [List.filter is_factb];
try reflexivity;
try (apply prune_zf_nofacts; [reflexivity|reflexivity|]); nfcrush.
Qed.
Lemma prune1pc_facts : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "Q@'8'XO%211'[1'ZK'9'X<'4%811';'>'K%2211%411'E&\4&XI&7'ZO%C11%:2B1&Z>r8r7r6r5r4r3r2r1%9887654321%>3;G1%?3N=1%B3Q0A1(5(:%11Q3%33Q4:1%G3Q5F1%I3Q561piNK1pk<Q11pQNQ91pQP:Q51poHQ71poNQ91pnJQ;1pi4Q=1").
Proof.
intros allkn sp wa w wv K hints br2. unfold prune1pc.
destruct K as [[kb kk] w' v|[kb kk] len|[kb kk] len bk|lo hi|e m|e lo hi|[kb kk] n|a1 n1 a2 n2|[kb kk] len c|[kb kk] len];
try apply prune1p_facts.
- destruct (expr_eqb kb (a_base wa)); [apply prune1p_facts|]. nfcrush.
- destruct (expr_eqb kb (a_base wa)); [apply prune1p_facts|].
unfold kzero_cut. destruct (ranges_apart_pc _ _ _ _ _ _ _ _ _); [reflexivity|].
destruct (kcut KZero allkn (a_base wa) (a_off wa) (elen w) kb kk len) eqn:E; [nfcrush|].
cbn [fst]. rewrite <- E. apply kcut_nofacts. reflexivity.
- destruct (expr_eqb kb (a_base wa)); [apply prune1p_facts|]. nfcrush.
- destruct (expr_eqb kb (a_base wa)); [apply prune1p_facts|].
unfold kfill_cut. destruct (ranges_apart_pc _ _ _ _ _ _ _ _ _); [reflexivity|].
destruct (kcut (fun a n => KFill a n c) allkn (a_base wa) (a_off wa) (elen w) kb kk len) eqn:E; [nfcrush|].
cbn [fst]. rewrite <- E. apply kcut_nofacts. reflexivity.
- destruct (expr_eqb kb (a_base wa)); [apply prune1p_facts|].
unfold kunk_cut. destruct (ranges_apart_pc _ _ _ _ _ _ _ _ _); [reflexivity|].
destruct (kcut KUnk allkn (a_base wa) (a_off wa) (elen w) kb kk len) eqn:E; [nfcrush|].
cbn [fst]. rewrite <- E. apply kcut_nofacts. reflexivity.
Qed.
Lemma prunepc_facts : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "Q>'8'XO%211'[1'ZK'9'X<'4%811'>';'K%3211%311%5281%?11'E&\4&XI&7'ZO%E11%=2D1&ZAr8r7r6r5r4r3r2r1%9887654321%>3;I1%?3Q0=1%B3Q2A1%C3Q3B7%E3Q321pj2G1pk<O1pl:Q61pQP:Q31poHQ51poNQ71pnJQ91pi4Q;1").
Proof.
intros allkn sp wa w wv kn. induction kn as [|K rest IH]; intros hints cache; [reflexivity|].
cbn [prunepc].
destruct (match kbase K with Some kb => match br_lookup cache kb with Some r => (r, cache) | None => (base_range allkn kb, (kb, base_range allkn kb) :: cache) end | None => (None, cache) end) as [br2 cache'].
destruct (prune1pc allkn sp wa w wv K hints br2) as [[kept scs1] hs1] eqn:E1.
destruct (prunepc allkn sp wa w wv rest hs1 cache') as [[r scs2] hs2] eqn:E2.
cbn [fst]. rewrite List.filter_app. pose proof (prune1pc_facts allkn sp wa w wv K hints br2) as H1. rewrite E1 in H1. cbn [fst] in H1.
rewrite H1. specialize (IH hs1 cache'). rewrite E2 in IH. cbn [fst] in IH. rewrite IH. cbn [List.filter]. destruct (is_factb K); reflexivity.
Qed.
Lemma carry_facts : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "L'8'ZM%211'XO%411'4%611'E&\4&XI&7'ZO%<11'>%12:2&WKr3r2r1%43321%:36>1%;3A91%>3C=1%?3D>6%A3D21pk<C1pl:F1plNI1").
Proof.
intros log kn hints. induction log as [|[a w v] older IH]; [reflexivity|].
cbn [carry]. destruct (carry older kn hints) as [[kn1 scs1] hs1]. cbn [fst] in IH.
destruct (prunepc _ _ _ _ _ kn1 hs1 []) as [[kn2 scs2] hs2] eqn:E.
cbn [fst List.filter is_factb]. pose proof (prunepc_facts (facts_of kn1) (mk_sprep (facts_of kn1) (a_base a) (a_off a) (elen w)) a w v kn1 hs1 []) as H.
rewrite E in H. cbn [fst] in H. rewrite H. exact IH.
Qed.
Fixpoint carryB (bc : bctx) (log : list sentry) (kn : list kentry) (hints : list bool)
: list kentry * list sidecond * list bool :=
match log with
| [] => (kn, [], hints)
| SE a w v :: older =>
let '(kn1, scs1, hs1) := carryB bc older kn hints in
let '(kn2, scs2, hs2) := prunepcB bc (mk_sprepB bc (a_base a) (a_off a) (elen w)) a w v kn1 hs1 [] in
(KWord a w v :: kn2, scs1 ++ scs2, hs2)
end.
Lemma carryB_eq : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "L'8'ZM%211'XO%411'4%611'E'>'ZO%:11%3271%4216&R9&UB&XAr2%211%411r3r1%843251&WK%13473%A3<31pk<C1pl:F1plNI1").
Proof.
intros log kn hints. induction log as [|[a w v] older IH]; [reflexivity|].
cbn [carryB carry]. rewrite IH.
pose proof (carry_facts older kn hints) as HF.
destruct (carry older kn hints) as [[kn1 scs1] hs1]. cbn [fst] in HF.
rewrite !facts_of_filter, <- HF, <- !facts_of_filter.
(repeat first [ rewrite mk_sprepB_eqf | rewrite prunepcB_eqf ]). reflexivity.
Qed.
Lemma p_aluop_eqb_refl : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "9'Q0'E'4&WCr1%2211(A%63521pi081"). Proof. intros []; reflexivity. Qed.
Lemma p_mulop_eqb_refl : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "9'Q4'E'4&Z:r1%2211(A%63521pi081"). Proof. intros []; reflexivity. Qed.
Lemma p_expr_eqb_refl : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "9'X<'E'4&X=r1%2211(A%63521pQP<81").
Proof.
induction x; cbn -[Z.eqb Nat.eqb]; rewrite ?p_aluop_eqb_refl, ?p_mulop_eqb_refl, ?IHx, ?IHx1, ?IHx2, ?Z.eqb_refl, ?Nat.eqb_refl, ?Bool.eqb_reflx; reflexivity.
Qed.
Lemma p_prune1pc_eq : forall allkn sp wa w wv K hints br2,
match kbase K with Some kb => br2 = base_range allkn kb | None => True end ->
prune1pc allkn sp wa w wv K hints br2 = prune1p allkn sp wa w wv K hints.
Proof.
intros allkn sp wa w wv K hints br2 Hb.
destruct K as [[kb kk] w' v|[kb kk] len|[kb kk] len bk|lo hi|e' m'|e' lo' hi'|[eb ek] en|c1 m1 c2 m2|[kb kk] len fc|[kb kk] len];
cbn [kbase] in Hb; try reflexivity; subst br2; unfold prune1pc, prune1p, prune_zf, kzero_cut, kfill_cut, kunk_cut;
destruct (expr_eqb kb (a_base wa)); reflexivity.
Qed.
Definition p_br_cache_ok (allkn : list kentry) (c : list (expr * option (Z * Z))) : Prop :=
Forall (fun p => snd p = base_range allkn (fst p)) c.
Lemma p_br_lookup_ok : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "Q1'8'XO%211'>'X<';'K%4211%311%6251%:11&UNr4r3%3221'E%;18&WI%1265(2r2%22=1%73641&WHr6%221=%;3B=1p051p0>1pmJE1pi:J1pj0E1pi4N1").
Proof.
intros allkn c b r Hc. induction c as [|[b' r'] rest IH]; cbn; [discriminate|].
apply Forall_cons_iff in Hc as [H1 Hc]. cbn in H1.
destruct (expr_eqb b b') eqn:E.
- intros H. injection H as <-. apply p_expr_eqb_eq in E. subst b'. exact H1.
- apply IH. exact Hc.
Qed.
Lemma p_prunepc_eq : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "Q>'8'XO%211'[1'ZK'9'X<'4%811'>';'K%3211%311%5281%?11&UNr8r1%3221'E'ZO%F11%>2E1%?21@&ZAr9r7r6r5r4r3r2%887@654321&Z@%179B87654%@3<31p0B1pj2G1pk<O1pl:Q61pQP:Q31poHQ51poNQ71pnJQ91pi4Q;1").
Proof.
intros allkn sp wa w wv kn. induction kn as [|K rest IH]; intros hints cache Hc; [reflexivity|].
cbn [prunepc prunep].
destruct (kbase K) as [kb|] eqn:HK.
- destruct (br_lookup cache kb) as [r|] eqn:HL.
+ rewrite (p_prune1pc_eq allkn sp wa w wv K hints r) by (rewrite HK; exact (p_br_lookup_ok _ _ _ _ Hc HL)).
destruct (prune1p allkn sp wa w wv K hints) as [[kept scs1] hs1]. rewrite (IH hs1 cache Hc). reflexivity.
+ rewrite (p_prune1pc_eq allkn sp wa w wv K hints (base_range allkn kb)) by (rewrite HK; reflexivity).
destruct (prune1p allkn sp wa w wv K hints) as [[kept scs1] hs1].
rewrite (IH hs1 ((kb, base_range allkn kb) :: cache)) by (constructor; [reflexivity | exact Hc]). reflexivity.
- rewrite (p_prune1pc_eq allkn sp wa w wv K hints None) by (rewrite HK; exact I).
destruct (prune1p allkn sp wa w wv K hints) as [[kept scs1] hs1]. rewrite (IH hs1 cache Hc). reflexivity.
Qed.
Definition g1 (fk : list kentry) (sp : sprep) (wa : saddr) (w : nat) (wv : expr) (K : kentry) : list kentry :=
fst (fst (prune1p fk sp wa w wv K [])).
Ltac pk_crush :=
cbn [fst snd];
first [ reflexivity
| match goal with
| |- context [if ?c then _ else _] => destruct c; pk_crush
| |- context [match ?h with ELit _ => _ | _ => _ end] => destruct h; pk_crush
| |- context [match ?h with Z0 => _ | _ => _ end] => destruct h; pk_crush
| |- context [match ?h with nil => _ | cons _ _ => _ end] => destruct h; pk_crush
end ].
Lemma prune1p_nil : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "Q6'8'XO%211'[1'ZK'9'X<'E'>'ZO%:11%3291'4%=11%6231&Z=r6r5r4r3r2r1(:%11;%978765431(=&S?%16;:9876%61C%44KC21%54CA17%H3A71pQNO1pQP:K1poHM1poNO1pnJQ11pjDQ31").
Proof.
intros. unfold g1, prune1p, prune_zf.
destruct K as [[kb kk] w' v|[kb kk] len|[kb kk] len bk|lo hi|e' m'|e' lo' hi'|[eb ek] en|c1 m1 c2 m2|[kb kk] len fc|[kb kk] len]; pk_crush.
Qed.
Lemma prunep_nil : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "Q8'8'XO%211'[1'ZK'9'X<'E'>'ZO%:11%3291'4%=11%6231&Z@r6r5r4r3r2r1(:%11;%978765431(=&\5&S?%15<;:98%34LL18%81E%64ME21%74EC19%J3C91pl:Q01pQP:M1poHO1poNQ11pnJQ31pjDQ51").
Proof.
intros fk sp wa w wv kn. induction kn as [|K rest IH]; [reflexivity|].
cbn [prunep flat_map]. rewrite prune1p_nil, IH. reflexivity.
Qed.
Inductive pk_res := PKeep | PRepl (l : list kentry).
Definition pk_list (K : kentry) (r : pk_res) : list kentry := match r with PKeep => [K] | PRepl l => l end.
Definition prune1pcK (bc : bctx) (sp : sprep) (wa : saddr) (w : nat) (wv : expr) (K : kentry) (same : bool)
(br2 : option (Z * Z)) : pk_res :=
let k := a_off wa in
let wb := a_base wa in
let zfK (mk : saddr -> expr -> kentry) (kb : expr) (kk : Z) (len : expr) :=
if same then
match len with
| ELit l0 => PRepl (ktrim mk kb kk l0 k w)
| _ => if Z.leb (k + Z.of_nat w) kk then PKeep else PRepl (kcutB bc mk wb k (elen w) kb kk len)
end
else if ranges_apart_pcB bc sp wb k (elen w) br2 kb kk len then PKeep
else match kcutB bc mk wb k (elen w) kb kk len with
| [] => if ranges_apart_pcB bc sp wb k (elen w) br2 kb kk len then PKeep else PRepl []
| cut => PRepl cut
end in
match K with
| KAlign _ _ | KRange _ _ _ | KWr _ _ | KDisj _ _ _ _ => PKeep
| KImg lo hi =>
match wb with
| ELit 0 =>
let r1 := if Z.ltb lo (Z.min k hi) then [KImg lo (Z.min k hi)] else [] in
let lo2 := Z.max lo (k + Z.of_nat w) in
let r2 := if Z.ltb lo2 hi then [KImg lo2 hi] else [] in
PRepl (r1 ++ r2)
| _ => if Z.ltb (hi - lo) (2 ^ 64) then
(if ranges_apart_pB bc sp wb k (elen w) (ELit 0) lo (ELit (hi - lo)) then PKeep else PRepl [])
else PRepl []
end
| KZero (SA kb kk) len => zfK KZero kb kk len
| KFill (SA kb kk) len c => zfK (fun a n => KFill a n c) kb kk len
| KUnk (SA kb kk) len => zfK KUnk kb kk len
| KWord (SA kb kk) w' v =>
if same then (if (Z.leb (kk + Z.of_nat w') k || Z.leb (k + Z.of_nat w) kk)%bool then PKeep else PRepl (kword_cut kb kk w' v k w))
else if ranges_apart_pcB bc sp wb k (elen w) br2 kb kk (elen w') then PKeep
else if (Nat.eqb w 1 && Nat.eqb w' 1 && expr_eqb wv v)%bool then PKeep
else if ranges_apart_pcB bc sp wb k (elen w) br2 kb kk (elen w') then PKeep else PRepl []
| KBlob (SA kb kk) len bk =>
if same then
match len with
| ELit l0 => let l := (l0 mod 2 ^ 64)%Z in
if (Z.leb (kk + l) k || Z.leb (k + Z.of_nat w) kk)%bool then PKeep else PRepl []
| _ => if Z.leb (k + Z.of_nat w) kk then PKeep else PRepl []
end
else if ranges_apart_pcB bc sp wb k (elen w) br2 kb kk len then PKeep else PRepl []
end.
Lemma prune1pcK_eq : forall fk sp wa w wv K br2 same,
(match kbase K with Some kb => same = expr_eqb kb (a_base wa) | None => True end) ->
pk_list K (prune1pcK (mkbc fk) sp wa w wv K same br2) = fst (fst (prune1pc fk sp wa w wv K [] br2)).
Proof.
intros fk sp wa w wv K br2 same H.
destruct K as [[kb kk] w' v|[kb kk] len|[kb kk] len bk|lo hi|e' m'|e' lo' hi'|[eb ek] en|c1 m1 c2 m2|[kb kk] len fc|[kb kk] len];
cbn [kbase] in H; try subst same; unfold prune1pcK, prune1pc, prune1p, prune_zf, kzero_cut, kfill_cut, kunk_cut;
(repeat first [ rewrite ranges_apart_pB_eqf | rewrite kcutB_eqf | rewrite ranges_apart_pcB_eqf ]); cbn [a_base a_off]; pk_crush.
Qed.
Definition bkey (e : expr) : option nat := first_var e.
Record binfo := BI { bi_base : expr; bi_br : option (Z * Z) }.
Record ntab := NT { nt_vars : list (list (expr * positive)); nt_other : list (expr * positive); nt_next : positive; nt_info : ptree binfo }.
Definition nt_empty : ntab := NT [] [] xH PTLeaf.
Fixpoint alookupE (l : list (expr * positive)) (b : expr) : option positive :=
match l with
| [] => None
| (b', id) :: rest => if expr_eqb b b' then Some id else alookupE rest b
end.
Definition nt_bucket (t : ntab) (k : option nat) : list (expr * positive) :=
match k with Some n => lget (nt_vars t) n | None => nt_other t end.
Definition nt_add (t : ntab) (k : option nat) (p : expr * positive) (bi : binfo) : ntab :=
match k with
| Some n => NT (lset (nt_vars t) n p) (nt_other t) (Pos.succ (nt_next t)) (pt_set (nt_next t) bi (nt_info t))
| None => NT (nt_vars t) (p :: nt_other t) (Pos.succ (nt_next t)) (pt_set (nt_next t) bi (nt_info t))
end.
Definition intern (bc : bctx) (t : ntab) (b : expr) : positive * binfo * ntab :=
let k := bkey b in
match alookupE (nt_bucket t k) b with
| Some id => (id, match pt_get (nt_info t) id with Some bi => bi | None => BI b (base_rangeB bc b) end, t)
| None => let id := nt_next t in
let bi := BI b (base_rangeB bc b) in
(id, bi, nt_add t k (b, id) bi)
end.
Definition NTI (bc : bctx) (t : ntab) : Prop :=
(forall k b id, In (b, id) (nt_bucket t k) ->
k = bkey b /\ pt_get (nt_info t) id = Some (BI b (base_rangeB bc b)) /\ (id < nt_next t)%positive)
/\ (forall k b id id', In (b, id) (nt_bucket t k) -> In (b, id') (nt_bucket t k) -> id = id').
Lemma nt_bucket_empty : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "B';'9%211'E'8'>'X<'L%3221%511&UG&UHr1%3221(:%117%=3731pkL?1").
Proof. intros [n|]; cbn; [unfold lget; destruct n; reflexivity | reflexivity]. Qed.
Lemma NTI_empty : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "6'R6&Q:r1&UH%3221pi@51").
Proof. intros bc. split; intros; rewrite nt_bucket_empty in *; contradiction. Qed.
Lemma alookupE_Some : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "J'8'>'X<'L%3221%511'E';%115&QLr3r2%3221(2r1%22<1%:3841&\3(=%14A@98r4%43A21p061pk@D1pi:F1pl>D1").
Proof.
induction l as [|[b' id'] rest IH]; cbn; intros b id H; [discriminate|].
destruct (expr_eqb b b') eqn:E.
- injection H as <-. apply p_expr_eqb_eq in E. subst. left. reflexivity.
- right. apply IH. exact H.
Qed.
Lemma alookupE_None : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "K'8'>'X<'L%3221%511'E';%115&QLr3r2%3221(0%11;%93731&G&\3(=%14A@98r4%43A21%611p081pk@E1pi:G1pl>E1").
Proof.
induction l as [|[b' id'] rest IH]; cbn; intros b id H; [tauto|].
destruct (expr_eqb b b') eqn:E; [discriminate|].
intros [X|X].
- injection X as -> ->. rewrite p_expr_eqb_refl in E. discriminate.
- exact (IH _ _ H X).
Qed.
Lemma nt_add_bucket : forall t k p bi k',
nt_bucket (nt_add t k p bi) k' = if okey_eqb k' k then p :: nt_bucket t k' else nt_bucket t k'.
Proof.
intros t [n|] p bi [m|]; cbn [nt_add nt_bucket nt_vars nt_other okey_eqb]; try reflexivity. apply lget_lset.
Qed.
Lemma nt_add_next : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "J'UK';'9%211'>'X<'L%3221'R7'E&UJ&UFr4r3r2r1%544321%711&\9%917%211%<3?41piB>1pmF@1pkLE1po<I1").
Proof. intros t [n|] p bi; reflexivity. Qed.
Lemma nt_add_info : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "N'UK';'9%211'>'X<'L%3221'R7'E'ZC%113&UI&UFr4r3r2r1%544321%711&ZB&UJ%118%;19%44@271%@3>61piBB1pmFD1pkLI1po<M1").
Proof. intros t [n|] p bi; reflexivity. Qed.
Lemma intern_ok : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "QN'R6'UK'X<'L'R7&Q:r6r5%3221'E'>%1287%221;&SJr7%23198(=r4r3%34@?21r2%54:D21%=3:71'Dr8%D217(Q7&R1%124F%32G1%E3J=1&\3%F2NM%A4ONKJ&UG&R8%11N%32C1%73651';'9%211r1r9%:21H%>3=31%<2Q8L%@3?K1p031pmFA1pkL91%L2=1%M2F1%N2L1p0Q01p0Q?1po>QG1piBQE1pk@QG1pi:QI1po<QK1pi@QM1").
Proof.
intros bc t b id bi t' [HA HB] H. unfold intern in H.
destruct (alookupE (nt_bucket t (bkey b)) b) as [id0|] eqn:HL.
- injection H as <- <- <-. pose proof (alookupE_Some _ _ _ HL) as HIn.
destruct (HA _ _ _ HIn) as (_ & Hinfo & _). rewrite Hinfo.
split; [split; assumption|]. split; [reflexivity|]. split; [exact HIn|]. intros; assumption.
- injection H as <- <- <-.
split; [|split; [reflexivity|split]].
+ split.
* intros k b0 id0 HIn. rewrite nt_add_bucket in HIn. rewrite nt_add_info, nt_add_next.
destruct (okey_eqb_spec k (bkey b)) as [->|NE].
-- destruct HIn as [X|X].
++ injection X as <- <-. split; [reflexivity|]. rewrite pt_gss. split; [reflexivity|lia].
++ destruct (HA _ _ _ X) as (H1 & H2 & H3). split; [exact H1|].
rewrite pt_gso by lia. split; [exact H2|lia].
-- destruct (HA _ _ _ HIn) as (H1 & H2 & H3). split; [exact H1|]. rewrite pt_gso by lia. split; [exact H2|lia].
* intros k b0 id0 id0' H1 H2. rewrite nt_add_bucket in H1, H2.
destruct (okey_eqb_spec k (bkey b)) as [->|NE]; [|exact (HB _ _ _ _ H1 H2)].
destruct H1 as [X1|X1]; destruct H2 as [X2|X2].
-- congruence.
-- injection X1 as <- <-. exfalso. exact (alookupE_None _ _ _ HL X2).
-- injection X2 as <- <-. exfalso. exact (alookupE_None _ _ _ HL X1).
-- exact (HB _ _ _ _ X1 X2).
+ rewrite nt_add_bucket. destruct (okey_eqb_spec (bkey b) (bkey b)); [|congruence]. left. reflexivity.
+ intros k p HIn. rewrite nt_add_bucket. destruct (okey_eqb_spec k (bkey b)); [right|]; exact HIn.
Qed.
Lemma nt_same_eq : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "Q9'R6'UK'X<'L&Q:r6r5%3221&\3'>%1287(=r4%24;:71&UG&R8%11:%32<1%:3851r3%94BA81r7%71:%9221%@3>41'E'4&\7%12G@&X=%129H%63531p081p0?1p0K1pkDQ01pi>Q21pkBQ21pi<Q41po<Q61pi@Q81").
Proof.
intros bc t b1 id1 b2 id2 [HA HB] H1 H2.
destruct (HA _ _ _ H1) as (_ & I1 & _). destruct (HA _ _ _ H2) as (_ & I2 & _).
destruct (Pos.eqb_spec id1 id2) as [<-|NE].
- rewrite I1 in I2. injection I2 as <-. symmetry. apply p_expr_eqb_refl.
- destruct (expr_eqb b1 b2) eqn:E; [|reflexivity]. exfalso. apply NE.
apply p_expr_eqb_eq in E. subst b2. exact (HB _ _ _ _ H1 H2).
Qed.
Record stx := STX { sx_a : saddr; sx_w : nat; sx_v : expr; sx_sp : sprep; sx_bid : positive; sx_br : option (Z * Z) }.
Fixpoint mk_stxs (bc : bctx) (log : list sentry) (t : ntab) : list stx * ntab :=
match log with
| [] => ([], t)
| SE a w v :: older =>
let '(sxs, t1) := mk_stxs bc older t in
let '(r, t2) := intern bc t1 (a_base a) in
let '(bid, bi) := r in
(sxs ++ [STX a w v (mk_sprepB bc (a_base a) (a_off a) (elen w)) bid (bi_br bi)], t2)
end.
Definition obrB (bc : bctx) (K : kentry) : option (Z * Z) :=
match kbase K with Some kb => base_rangeB bc kb | None => None end.
Definition g1cB (bc : bctx) (sx : stx) (K : kentry) : list kentry :=
fst (fst (prune1pcB bc (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) K [] (obrB bc K))).
Fixpoint chain_slow (bc : bctx) (sxs : list stx) (l : list kentry) : list kentry :=
match sxs with
| [] => l
| sx :: rest => chain_slow bc rest (flat_map (g1cB bc sx) l)
end.
Fixpoint chainK (bc : bctx) (sxs : list stx) (K : kentry) (same_of : positive -> bool) (br2 : option (Z * Z)) : list kentry :=
match sxs with
| [] => [K]
| sx :: rest =>
match prune1pcK bc (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) K (same_of (sx_bid sx)) br2 with
| PKeep => chainK bc rest K same_of br2
| PRepl l => chain_slow bc rest l
end
end.
Fixpoint chainK2 (bc : bctx) (sxs : list stx) (K : kentry) (okb : option expr) (same_of : positive -> bool) (br2 : option (Z * Z)) : list kentry :=
match sxs with
| [] => [K]
| sx :: rest =>
match prune1pcK bc (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) K (same_of (sx_bid sx)) br2 with
| PKeep => chainK2 bc rest K okb same_of br2
| PRepl l =>
match okb with
| Some kb =>
flat_map (fun K' => match kbase K' with
| Some kb' => if expr_eqb kb' kb then chainK2 bc rest K' okb same_of br2 else chain_slow bc rest [K']
| None => chain_slow bc rest [K']
end) l
| None => chain_slow bc rest l
end
end
end.
Fixpoint entriesV (bc : bctx) (sxs : list stx) (kn : list kentry) (t : ntab) : list kentry :=
match kn with
| [] => []
| K :: rest =>
match kbase K with
| Some kb => let '(r, t') := intern bc t kb in
let '(bid, bi) := r in
chainK2 bc sxs K (Some kb) (Pos.eqb bid) (bi_br bi) ++ entriesV bc sxs rest t'
| None => chainK2 bc sxs K None (fun _ => false) None ++ entriesV bc sxs rest t
end
end.
Fixpoint stores_part (bc : bctx) (sxs : list stx) : list kentry :=
match sxs with
| [] => []
| sx :: newer => stores_part bc newer ++ chainK2 bc newer (KWord (sx_a sx) (sx_w sx) (sx_v sx)) (Some (a_base (sx_a sx))) (Pos.eqb (sx_bid sx)) (sx_br sx)
end.
Definition carryV (bc : bctx) (log : list sentry) (kn : list kentry) : list kentry :=
let '(sxs, t) := mk_stxs bc log nt_empty in
stores_part bc sxs ++ entriesV bc sxs kn t.
Definition carryK0 (bc : bctx) (log : list sentry) (kn : list kentry) (hints : list bool)
: list kentry * list sidecond * list bool :=
match log, hints with
| [], _ => (kn, [], hints)
| _, [] => (carryV bc log kn, [], [])
| _, _ => carryB bc log kn hints
end.
Definition FM (fk : list kentry) (s : sentry) (l : list kentry) : list kentry :=
match s with SE a w v => flat_map (g1 fk (mk_sprep fk (a_base a) (a_off a) (elen w)) a w v) l end.
Fixpoint chainRo (fk : list kentry) (sxo : list sentry) (l : list kentry) : list kentry :=
match sxo with [] => l | s :: newer => chainRo fk newer (FM fk s l) end.
Definition kw (s : sentry) : kentry := match s with SE a w v => KWord a w v end.
Fixpoint SPRo (fk : list kentry) (sxo : list sentry) : list kentry :=
match sxo with [] => [] | s :: newer => SPRo fk newer ++ chainRo fk newer [kw s] end.
Lemma flat_map_app' : forall (A B : Type) (f : A -> list B) l1 l2, flat_map f (l1 ++ l2) = flat_map f l1 ++ flat_map f l2.
Proof. intros. rewrite !flat_map_concat_map, map_app, concat_app. reflexivity. Qed.
Lemma FM_app : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "E'8'XO%211'ZM'E&Q9r4r3&3r2r1%33:21%73651%83764%93874%73>21%<3>41plD?1plB@1pn:@1pjDB1").
Proof. intros fk [a w v] l1 l2. unfold FM. apply flat_map_app'. Qed.
Lemma chainRo_snoc : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "J'8'XO%211'ZM%411'E&R?r4&3r3(5r2(:%11:%43;31%73<61r1%;3:21&Q9%=3<:3%23=91%@3C41pl>D1pn:D1po8D1pjDG1").
Proof. intros fk sxo. induction sxo as [|x rest IH]; intros; [reflexivity|]. cbn [chainRo app]. apply IH. Qed.
Lemma chainRo_app : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "F'8'XO%211'ZM%411'E&R?r4r3&3r2r1%33;21%73651%83764%93874%73?21%<3?41plD@1plBA1po8@1pjDC1").
Proof. intros fk sxo. induction sxo as [|x rest IH]; intros; [reflexivity|]. cbn [chainRo]. rewrite FM_app. apply IH. Qed.
Lemma SPRo_snoc : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "K'8'XO%211'ZM%411'E&Q<r3&3r2(5r1(:%11:%43;31%73<61%:291&T7%117&Q9%>2=;%23>:1%<3E41%B3E71pn:E1po8E1pjDH1").
Proof.
intros fk sxo s. induction sxo as [|x rest IH]; [destruct s; reflexivity|].
cbn [SPRo app]. rewrite IH, chainRo_snoc, FM_app. reflexivity.
Qed.
Lemma carry_vertical : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "Q4'8'ZM%211'XO%411'E'>'ZO%811%3251'4%;11%6231&WKr2r1(:%117%53431(=&3&Q<&XA%118&\6%12H;%5231&R?%1353=%93J31%>1G%<4KG21%=4GE1?%L3E?1pl:N1plNQ11").
Proof.
intros log kn. induction log as [|[a w v] older IH]; [reflexivity|].
cbn [carry rev]. pose proof (carry_facts older kn []) as HF. rewrite IH in HF |- *. cbn [fst] in HF.
cbv beta iota zeta. rewrite !facts_of_filter in *. rewrite HF.
rewrite p_prunepc_eq by constructor. rewrite prunep_nil.
match goal with |- context [flat_map ?g ?l] => change (flat_map g l) with (FM (List.filter is_factb kn) (SE a w v) l) end.
rewrite FM_app, SPRo_snoc, chainRo_snoc. reflexivity.
Qed.
Definition strip (sx : stx) : sentry := SE (sx_a sx) (sx_w sx) (sx_v sx).
Definition SX_OK (bc : bctx) (t : ntab) (sx : stx) : Prop :=
In (a_base (sx_a sx), sx_bid sx) (nt_bucket t (bkey (a_base (sx_a sx))))
/\ sx_br sx = base_rangeB bc (a_base (sx_a sx))
/\ sx_sp sx = mk_sprepB bc (a_base (sx_a sx)) (a_off (sx_a sx)) (elen (sx_w sx)).
Lemma g1cB_eq : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "Q8'8'XO%211'V>'E'[1&VGr1%211&U@&UBr2%211&WA&VE%118%311&WB%113&X6&VI%11>%311%>4;751%D3C@1pl>GG&\5&S@r3%C11%321C%53NN1&Q9&V=%11G%3271%Q03;51p0=1po4Q31pjDQ51").
Proof.
intros fk sx Hsp. apply functional_extensionality; intros l. unfold FM, strip. f_equal.
apply functional_extensionality; intros K. unfold g1cB, obrB. rewrite Hsp. (repeat first [ rewrite base_rangeB_eqf | rewrite mk_sprepB_eqf | rewrite prune1pcB_eqf ]).
rewrite p_prune1pc_eq by (destruct (kbase K); reflexivity). rewrite prune1p_nil. reflexivity.
Qed.
Lemma chain_slow_eq : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "Q<'8'XO%211'V>%411'I'E'[1&VGr1%211&U@&UBr4%211&WA&VE%118%311&WB%113&X6&VI%11>%311%>4;751%D3C@1qo4H1r2%H3J21&R@r3%23B14&R?&J'ZM&V=%34Q2216%53I1:%Q13Q571p0;1pl>Q71po:Q61pjDQ91").
Proof.
intros fk sxs. induction sxs as [|sx rest IH]; intros l HF; [reflexivity|].
apply Forall_cons_iff in HF as [H1 HF]. cbn [chain_slow chainRo map]. rewrite (g1cB_eq _ _ H1). apply IH. exact HF.
Qed.
Lemma chainK_eq : forall fk sxs K same_of br2,
Forall (fun sx => sx_sp sx = mk_sprepB (mkbc fk) (a_base (sx_a sx)) (a_off (sx_a sx)) (elen (sx_w sx))) sxs ->
match kbase K with
| Some kb => br2 = base_rangeB (mkbc fk) kb /\ Forall (fun sx => same_of (sx_bid sx) = expr_eqb kb (a_base (sx_a sx))) sxs
| None => br2 = None
end ->
chainK (mkbc fk) sxs K same_of br2 = chain_slow (mkbc fk) sxs [K].
Proof.
intros fk sxs. induction sxs as [|sx rest IH]; intros K same_of br2 HS HK; [reflexivity|].
apply Forall_cons_iff in HS as [H1 HS]. cbn [chainK chain_slow flat_map]. rewrite app_nil_r.
unfold g1cB at 1.
assert (E : pk_list K (prune1pcK (mkbc fk) (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) K (same_of (sx_bid sx)) br2)
= fst (fst (prune1pcB (mkbc fk) (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) K [] (obrB (mkbc fk) K)))).
{ (repeat first [ rewrite prune1pcB_eqf ]). destruct (kbase K) as [kb|] eqn:HB.
- destruct HK as [-> HK]. apply Forall_cons_iff in HK as [HK1 HK].
unfold obrB. rewrite HB. apply prune1pcK_eq. rewrite HB. exact HK1.
- unfold obrB. rewrite HB. subst br2. apply prune1pcK_eq. rewrite HB. exact I. }
destruct (prune1pcK _ _ _ _ _ K _ br2) as [|l]; cbn [pk_list] in E.
- rewrite <- E. apply IH; [exact HS|]. destruct (kbase K) as [kb|]; [|exact HK].
destruct HK as [Hbr HK]. apply Forall_cons_iff in HK as [_ HK]. exact (conj Hbr HK).
- rewrite <- E. reflexivity.
Qed.
Lemma flat_map_flat_map : forall (A B C : Type) (f : A -> list B) (g : B -> list C) l,
flat_map g (flat_map f l) = flat_map (fun x => flat_map g (f x)) l.
Proof. intros. induction l as [|x r IH]; [reflexivity|]. cbn. rewrite flat_map_app', IH. reflexivity. Qed.
Lemma chain_slow_flat_map : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "I'R6'8'V>%211'XO%411'E&R@r3r2r1%43321&\5r4(5(:%11<%33=71%;35:1qQN?1%84@@1:%?3@:1pl>A1po:D1pi@H1").
Proof.
intros bc sxs. induction sxs as [|sx rest IH]; intros l.
- cbn. induction l as [|x r IHl]; [reflexivity|]. cbn. rewrite <- IHl. reflexivity.
- cbn [chain_slow]. rewrite IH. rewrite flat_map_flat_map.
f_equal. apply functional_extensionality. intros K. cbn [flat_map]. rewrite app_nil_r. rewrite <- IH. reflexivity.
Qed.
Lemma chainK2_eq : forall fk sxs K okb same_of br2,
Forall (fun sx => sx_sp sx = mk_sprepB (mkbc fk) (a_base (sx_a sx)) (a_off (sx_a sx)) (elen (sx_w sx))) sxs ->
okb = kbase K ->
match okb with
| Some kb => br2 = base_rangeB (mkbc fk) kb /\ Forall (fun sx => same_of (sx_bid sx) = expr_eqb kb (a_base (sx_a sx))) sxs
| None => br2 = None
end ->
chainK2 (mkbc fk) sxs K okb same_of br2 = chain_slow (mkbc fk) sxs [K].
Proof.
intros fk sxs. induction sxs as [|sx rest IH]; intros K okb same_of br2 HS Hokb HK; [reflexivity|].
apply Forall_cons_iff in HS as [H1 HS]. cbn [chainK2 chain_slow flat_map]. rewrite app_nil_r.
unfold g1cB at 1.
assert (E : pk_list K (prune1pcK (mkbc fk) (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) K (same_of (sx_bid sx)) br2)
= fst (fst (prune1pcB (mkbc fk) (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) K [] (obrB (mkbc fk) K)))).
{ (repeat first [ rewrite prune1pcB_eqf ]). unfold obrB. rewrite <- Hokb. destruct okb as [kb|].
- destruct HK as [-> HK]. apply Forall_cons_iff in HK as [HK1 HK]. apply prune1pcK_eq. rewrite <- Hokb. exact HK1.
- subst br2. apply prune1pcK_eq. rewrite <- Hokb. exact I. }
destruct (prune1pcK _ _ _ _ _ K _ br2) as [|l]; cbn [pk_list] in E; rewrite <- E.
- apply IH; [exact HS|exact Hokb|]. destruct okb as [kb|]; [|exact HK].
destruct HK as [Hbr HK]. apply Forall_cons_iff in HK as [_ HK]. exact (conj Hbr HK).
- destruct okb as [kb|]; [|reflexivity]. rewrite (chain_slow_flat_map _ rest l).
f_equal. apply functional_extensionality. intros K'.
destruct (kbase K') as [kb'|] eqn:HB'; [|reflexivity].
destruct (expr_eqb kb' kb) eqn:EQ; [|reflexivity].
apply p_expr_eqb_eq in EQ. subst kb'.
apply IH; [exact HS|symmetry; exact HB'|].
destruct HK as [Hbr HK]. apply Forall_cons_iff in HK as [_ HK]. exact (conj Hbr HK).
Qed.
Lemma SX_OK_mono : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "Q2'R6'UK'V>';'9%211'>'X<'L%3221&\3r1&UGr5r2%3221%63751r3%6251%93:51p041pmF<1pkLA1&Q=r4%23<1;r6%4313:p031p071po4L1po>N1po<O1pi@Q11").
Proof. intros bc t t' sx Hm (H1 & H2 & H3). split; [apply Hm; exact H1|]. split; assumption. Qed.
Lemma mk_stxs_ok : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "R2'8'XO%211'ZM%411'UK'V>%711&Q:&UBr5%211r3%5221'E'>%129;&UAr6%:11r4%432;1(=r2%24AC<1%;3941'Dr7%C11%E21A'I&Q=%124D%33K1=&J&V=%24NQ11@&\6%12Q3D%I3Q331';'9%211'X<'L%N221&\3r1&UG%12FJ%43531%32Q1Q7%637M1p031pmF91pkL=1%N2A1%O2H1%Q02M1p0Q21p0Q?1po>QH1po:QG1po<QJ1plNQL1pjDQO1").
Proof.
intros fk log. induction log as [|[a w v] older IH]; intros t sxs t' HT H.
- cbn in H. injection H as <- <-. split; [exact HT|]. split; [constructor|]. split; [reflexivity|]. intros; assumption.
- cbn [mk_stxs] in H. destruct (mk_stxs (mkbc fk) older t) as [sxs0 t1] eqn:E0.
destruct (intern (mkbc fk) t1 (a_base a)) as [[bid bi] t2] eqn:EI.
injection H as <- <-.
destruct (IH t sxs0 t1 HT E0) as (HT1 & HS & Hmap & Hm1).
destruct (intern_ok _ _ _ _ _ _ HT1 EI) as (HT2 & -> & HIn & Hm2).
split; [exact HT2|]. split.
+ apply Forall_app. split.
* apply Forall_impl with (P := SX_OK (mkbc fk) t1); [|exact HS]. intros sx. apply SX_OK_mono. exact Hm2.
* constructor; [|constructor]. split; [exact HIn|]. split; reflexivity.
+ split; [rewrite map_app, Hmap; reflexivity|]. intros k p Hp. apply Hm2. apply Hm1. exact Hp.
Qed.
Lemma Forall_SX_sp : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "Q8'8'XO%211'UK'V>%511'I&Q=&UBr3%211r2%5221r1%83:21'E'[1&VG%115&U@r5%=11&WA&VE%11;%311&WB%113&X6&VI%11A%311%=4;751%B3A?1qo4N1%M3O1Hp0F1po:Q01po<Q31pjDQ51").
Proof. intros fk t sxs H. apply Forall_impl with (P := SX_OK (mkbc fk) t); [|exact H]. intros sx (_ & _ & X). exact X. Qed.
Lemma Forall_SX_same : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "QI'8'XO%211'UK'V>%511'X<'L&Q:&UBr5%211r4%5221&\3'>%12:9(=r3r2%34>=21&UG&R8%115%32>1%;3951'I&Q=r7%D11r6%4221%63L1F'E'4&\7&VFr1%211%42M1&X=&WA&VE%116%311%52?1%=3<71qo4Q;1%F3Q<1Bp0A1p0I1p0Q61piDQ=1pl4Q?1po:QA1po<QD1pjDQF1").
Proof.
intros fk t sxs kb bid HT HIn H. apply Forall_impl with (P := SX_OK (mkbc fk) t); [|exact H].
intros sx (H1 & _ & _). exact (nt_same_eq _ _ _ _ _ _ HT HIn H1).
Qed.
Lemma entriesV_eq : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "Q6'8'XO%211'V>%411'UK&Q:&UBr4%211r1%5221'I&Q=r5%811r2%4221%63?1:'E&S2r6%?11r3%442:@1&R?&J'ZM&V=%34J21?%5391F%<3M71p0>1p0F1po<M1pl:Q11po:Q01pjDQ31").
Proof.
intros fk sxs kn. induction kn as [|K rest IH]; intros t HT HS.
- cbn. clear. induction sxs as [|sx r IH]; [reflexivity|]. cbn. destruct (strip sx). exact IH.
- cbn [entriesV]. change (K :: rest) with ([K] ++ rest). rewrite chainRo_app.
destruct (kbase K) as [kb|] eqn:HB.
+ destruct (intern (mkbc fk) t kb) as [[bid bi] t'] eqn:EI.
destruct (intern_ok _ _ _ _ _ _ HT EI) as (HT' & -> & HIn & Hm).
assert (HS' : Forall (SX_OK (mkbc fk) t') sxs).
{ apply Forall_impl with (P := SX_OK (mkbc fk) t); [|exact HS]. intros sx. apply SX_OK_mono. exact Hm. }
rewrite (IH t' HT' HS'). f_equal.
rewrite chainK2_eq; [apply chain_slow_eq; exact (Forall_SX_sp _ _ _ HS) | exact (Forall_SX_sp _ _ _ HS) | symmetry; exact HB |].
cbn [bi_br]. split; [reflexivity|]. exact (Forall_SX_same _ _ _ _ _ HT' HIn HS').
+ rewrite (IH t HT HS). f_equal.
rewrite chainK2_eq; [apply chain_slow_eq; exact (Forall_SX_sp _ _ _ HS) | exact (Forall_SX_sp _ _ _ HS) | symmetry; exact HB |].
reflexivity.
Qed.
Lemma stores_part_eq : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "Q3'8'XO%211'UK'V>%511&Q:&UBr3%211r2%5221'I&Q=r4%811%3218%53=17'E&V<r5%>11%321>&Q<&J'ZM&V=%34G21C%5281%;3K71p0=1p0D1po:K1po<N1pjDQ01").
Proof.
intros fk t sxs HT. induction sxs as [|sx newer IH]; intros HS; [reflexivity|].
apply Forall_cons_iff in HS as [H1 HS]. cbn [stores_part SPRo map]. rewrite (IH HS). f_equal.
destruct H1 as (HIn & Hbr & _). destruct (sx_a sx) as [b o] eqn:Ea. cbn [a_base a_off] in HIn, Hbr.
rewrite chainK2_eq; [unfold kw, strip; rewrite Ea; apply chain_slow_eq; exact (Forall_SX_sp _ _ _ HS) | exact (Forall_SX_sp _ _ _ HS) | reflexivity |].
cbn [a_base]. split; [exact Hbr|]. exact (Forall_SX_same _ _ _ _ _ HT HIn HS).
Qed.
Lemma carryK0_eq : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "L'8'ZM%211'XO%411'4%611'E'>'ZO%:11%3271%4216&R<&UB&XAr2%211%411r3r1%843251&WK%13473%A3<31pk<C1pl:F1plNI1").
Proof.
intros log kn hints. unfold carryK0. destruct log as [|s older]; [reflexivity|].
destruct hints as [|h hs]; [|apply carryB_eq].
rewrite carry_vertical. unfold carryV.
destruct (mk_stxs (mkbc (facts_of kn)) (s :: older) nt_empty) as [sxs t] eqn:E.
destruct (mk_stxs_ok _ _ _ _ _ (NTI_empty _) E) as (HT & HS & Hmap & _).
rewrite (stores_part_eq _ _ _ HT HS), (entriesV_eq _ _ _ _ HT HS), Hmap. reflexivity.
Qed.
Fixpoint pt_map {A B : Type} (f : A -> B) (t : ptree A) : ptree B :=
match t with
| PTLeaf => PTLeaf
| PTNode l o r => PTNode (pt_map f l) (match o with Some a => Some (f a) | None => None end) (pt_map f r)
end.
Lemma pt_get_map : forall (A B : Type) (f : A -> B) t k,
pt_get (pt_map f t) k = match pt_get t k with Some a => Some (f a) | None => None end.
Proof. intros A B f t. induction t as [|l IHl o r IHr]; intros k; [destruct k; reflexivity|]. destruct k; cbn; auto. Qed.
Definition kdescr (K : kentry) : option (expr * Z * option Z) :=
match K with
| KWord (SA kb kk) w _ => Some (kb, kk, Some (zlit64 (Z.of_nat w)))
| KZero (SA kb kk) len | KUnk (SA kb kk) len | KFill (SA kb kk) len _ | KBlob (SA kb kk) len _ =>
Some (kb, kk, match len with ELit z => Some (zlit64 z) | _ => None end)
| KImg lo hi => Some (ELit 0%Z, lo, if Z.ltb (hi - lo) (2 ^ 64) then Some (zlit64 (hi - lo)) else None)
| _ => None
end.
Record einfo := EI { ei_bid : positive; ei_gid : positive; ei_kb : expr; ei_br : option (Z * Z); ei_k : Z; ei_m : option Z }.
Definition gval : Type := (positive * option (Z * Z) * (Z * Z))%type.
Definition gtab := ptree gval.
Record gst := GST { gs_gid : ptree (ptree positive); gs_next : positive; gs_bnds : gtab }.
Definition gst_empty : gst := GST PTLeaf xH PTLeaf.
Definition gkey (kk : Z) : positive :=
let g := Z.shiftr kk 16 in Z.to_pos (if Z.leb 0 g then 2 * g + 1 else - (2 * g))%Z.
Definition ggroup (gs : gst) (bid : positive) (kk : Z) : positive * gst :=
let gk := gkey kk in
let inner := match pt_get (gs_gid gs) bid with Some i => i | None => PTLeaf end in
match pt_get inner gk with
| Some gid => (gid, gs)
| None => let gid := gs_next gs in
(gid, GST (pt_set bid (pt_set gk gid inner) (gs_gid gs)) (Pos.succ gid) (gs_bnds gs))
end.
Definition bnd_add (gs : gst) (gid bid : positive) (obr : option (Z * Z)) (lo hi : Z) : gst :=
GST (gs_gid gs) (gs_next gs)
(match pt_get (gs_bnds gs) gid with
| Some (b, o, (l, h)) => pt_set gid (b, o, (Z.min l lo, Z.max h hi)) (gs_bnds gs)
| None => pt_set gid (bid, obr, (lo, hi)) (gs_bnds gs)
end).
Fixpoint scan_entries (bc : bctx) (kn : list kentry) (t : ntab) (gs : gst) : list (option einfo) * ntab * gst :=
match kn with
| [] => ([], t, gs)
| K :: rest =>
match kdescr K with
| Some (kb, kk, om) =>
let '(r, t1) := intern bc t kb in
let '(bid, bi) := r in
let '(gid, gs1) := match om with
| Some m => let '(gid, gs0) := ggroup gs bid kk in (gid, bnd_add gs0 gid bid (bi_br bi) kk (kk + m)%Z)
| None => (xH, gs)
end in
let '(infos, t2, gs2) := scan_entries bc rest t1 gs1 in
(Some (EI bid gid kb (bi_br bi) kk om) :: infos, t2, gs2)
| None =>
let '(infos, t2, gs2) := scan_entries bc rest t gs in
(None :: infos, t2, gs2)
end
end.
Definition sx_m1 (sx : stx) : Z := zlit64 (Z.of_nat (sx_w sx)).
Definition verdict (sx : stx) (g : gval) : bool :=
match g with
| (b, obr, (glo, ghi)) =>
if Pos.eqb b (sx_bid sx) then false else
match sp_rng (sx_sp sx), obr with
| Some (lo1, hi1), Some (lo2, hi2) =>
(Z.leb (hi1 + a_off (sx_a sx) + sx_m1 sx - lo2) glo || Z.leb ghi (lo1 + a_off (sx_a sx) - hi2))%bool
| _, _ => false
end
end.
Fixpoint mk_fl (g : gval) (sxs : list stx) : list (stx * list stx) :=
match sxs with
| [] => []
| sx :: rest => if verdict sx g then mk_fl g rest else (sx, rest) :: mk_fl g rest
end.
Definition gfl : Type := (gval * list (stx * list stx))%type.
Definition mk_gl (bnds : gtab) (sxs : list stx) : ptree gfl := pt_map (fun g => (g, mk_fl g sxs)) bnds.
Definition obr_eqb (a b : option (Z * Z)) : bool :=
match a, b with
| Some (x1, y1), Some (x2, y2) => Z.eqb x1 x2 && Z.eqb y1 y2
| None, None => true
| _, _ => false
end%bool.
Definition inb (g : gval) (ei : einfo) : bool :=
match ei_m ei, g with
| Some m, (b, obr, (lo, hi)) =>
Pos.eqb b (ei_bid ei) && obr_eqb obr (ei_br ei) && Z.leb lo (ei_k ei) && Z.leb (ei_k ei + m) hi
| _, _ => false
end%bool.
Fixpoint chainKF (bc : bctx) (fl : list (stx * list stx)) (K : kentry) (okb : option expr) (same_of : positive -> bool)
(br2 : option (Z * Z)) : list kentry :=
match fl with
| [] => [K]
| (sx, rest) :: fl' =>
match prune1pcK bc (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) K (same_of (sx_bid sx)) br2 with
| PKeep => chainKF bc fl' K okb same_of br2
| PRepl l =>
match okb with
| Some kb =>
flat_map (fun K' => match kbase K' with
| Some kb' => if expr_eqb kb' kb then chainK2 bc rest K' okb same_of br2 else chain_slow bc rest [K']
| None => chain_slow bc rest [K']
end) l
| None => chain_slow bc rest l
end
end
end.
Fixpoint entriesG (bc : bctx) (sxs : list stx) (gl : ptree gfl) (kn : list kentry) (infos : list (option einfo)) : list kentry :=
match kn, infos with
| K :: rest, oi :: irest =>
(match oi with
| Some ei =>
let okb := kbase K in
let same_of := match okb with Some _ => Pos.eqb (ei_bid ei) | None => fun _ => false end in
let br2 := match okb with Some _ => ei_br ei | None => None end in
match pt_get gl (ei_gid ei) with
| Some (g, fl) => if inb g ei then chainKF bc fl K okb same_of br2 else chainK2 bc sxs K okb same_of br2
| None => chainK2 bc sxs K okb same_of br2
end
| None => chainK2 bc sxs K None (fun _ => false) None
end) ++ entriesG bc sxs gl rest irest
| _, _ => []
end.
Definition carryG (bc : bctx) (log : list sentry) (kn : list kentry) : list kentry :=
let '(sxs, t0) := mk_stxs bc log nt_empty in
let '(r, gs) := scan_entries bc kn t0 gst_empty in
let '(infos, _) := r in
stores_part bc sxs ++ entriesG bc sxs (mk_gl (gs_bnds gs) sxs) kn infos.
Lemma zlit64_idem : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "8'K'E&\1r1%211%311%53612pQPB71").
Proof.
intros z. unfold zlit64. destruct (Z.leb 0 z && Z.ltb z two64)%bool eqn:E; [rewrite E; reflexivity|].
pose proof (Z.mod_pos_bound z two64 ltac:(unfold two64; lia)) as B.
replace (Z.leb 0 (z mod two64) && Z.ltb (z mod two64) two64)%bool with true; [reflexivity|].
symmetry. apply andb_true_intro. split; [apply Z.leb_le|apply Z.ltb_lt]; lia.
Qed.
Lemma kdescr_kbase : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "QE'XO'X<'K';%112'E'>%1265%2214%611&SMr4%211(2(=r3r2%34@?21r1%54<?21%72<1%@3<91'H%D1F&XKr5%211%>2J@%G3521'F'Dr7(W=%12A?%M3Q231r6(W<z%211%Q23Q641%Q33Q6?H%;221%<281qk6Q91%?2Q:1qlHQ;1%A2Q<1%I2C1p0K1pmBQ=1pl6Q@1pl4QB1pQNQD1").
Proof.
intros K kb kk om H.
destruct K as [[b k] w' v|[b k] len|[b k] len bk|lo hi|e' m'|e' lo' hi'|[b k] n|a1 n1 a2 n2|[b k] len fc|[b k] len];
cbn [kdescr kbase] in *; try discriminate; try (injection H as <- <- Hm); try (left; reflexivity).
right. exists lo, hi. repeat split; congruence.
Qed.
Lemma kdescr_None_kbase : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "H'XO'E';'>'X<'K%3221%512%5221%711&SMr1%211(0%116%>3631%>1<&XKr2%211%71@%D3521p071pQNG1").
Proof.
intros K H. destruct K as [[b k] w' v|[b k] len|[b k] len bk|lo hi|e' m'|e' lo' hi'|[b k] n|a1 n1 a2 n2|[b k] len fc|[b k] len];
cbn [kdescr kbase] in *; try discriminate; reflexivity.
Qed.
Lemma prune1pcK_keep_based : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "S8'R6'[1'ZK'9'X<'XO'K'E';%115&XKr8%211(2r7%22;1%93741'>%12><%;1=%3221%=11&SMr9%211(=%14FD?<r6%?2F1%44;:31%A2:1%H3:71'4&X=&WAr=%211%42>1(6%Q03721%G2Q2Q2%Q111&[0r?%211%D4Q7Q7OB%Q1261%Q83631&R1rAr;%3221r5%L4Q?Q?J1%Q92>1%Q@3>41'H&\<&\:&WBr@%211%42QC1&\1&\>%11F%311%9251%:2QFB%<221%<2Q;Dr:%>221%?2QB<%A221%C261'UO&V2rCrBr>%Q123Q>%5843Q1FQ72Q<1(Q;%R=3821p0:1p0O1p0Q81p0QA1p0QJ1p0R:1pk:RE1plLRF1pk8RG1plJRH1pm0RI1pl6RJ1pl4RM1pQNRM1pQP:RO1poHS11poNS31pnJS51pi@S71").
Proof.
intros bc sp wa w wv K kb kk m lo1 hi1 lo2 hi2 HB HD Hne Hsp Hbr Hnum.
destruct K as [[b k] w' v|[b k] len|[b k] len bk|lo hi|e' m'|e' lo' hi'|[b k] n|a1 n1 a2 n2|[b k] len fc|[b k] len];
cbn [kbase kdescr] in HB, HD; try discriminate; injection HB as ->;
try (injection HD as <- <-); try (destruct len as [z| | | | | | |]; try discriminate; injection HD as <- <-);
unfold prune1pcK; cbn [a_base a_off]; unfold ranges_apart_pcB; cbn [elen]; rewrite Hne, Hsp, Hbr;
match goal with |- context [if ((?a <=? ?b) || (?c <=? ?d))%Z then _ else _] =>
replace ((a <=? b) || (c <=? d))%Z%bool with true; [reflexivity|];
symmetry; apply Bool.orb_true_iff; destruct Hnum as [H|H]; [left|right]; apply Z.leb_le; rewrite ?zlit64_idem; lia end.
Qed.
Lemma prune1pcK_keep_img : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "S6'R6'[1'ZK'9'X<'K'4';'>%1244%311'E%4287%618%6221%811&SM(W=r9r8%3221%511(2(=(W<z%211%44GF19r7%72H1%74BA31%92A1%E3A;1&X=&WAr=%211%42;1(6%L3Q121&[0r?%211%D4Q6Q6H?%F2Q31%Q23Q331&R1rA%221Fr6%K4Q=Q=F1%M2Q:1%Q93Q:41'H&\<&\:&WBr@%211%42Q91&\1&\>%11E%311%9251%:2Q>N%<221%<2Q7Q0r;%>221r:%@21=%B231%D271'UO&V2rCrBr>%QN21Q<%5843Q1GQ71QDO(Q;%R73821p0:1p0Q01p0Q81p0Q?1p0QG1piNR>1pn<RC1pk:RE1plLRF1pk8RG1plJRH1pm0RI1pk6RJ1plHRK1pQP:RM1poHRO1poNS11pnJS31pi@S51").
Proof.
intros bc sp wa w wv lo hi m lo1 hi1 lo2 hi2 same br2 HD Hne Hsp Hbr Hnum.
cbn [kdescr] in HD. destruct (Z.ltb (hi - lo) (2 ^ 64)) eqn:Hlt; [|discriminate]. injection HD as <-.
unfold prune1pcK. destruct wa as [wb k]. cbn [a_base a_off] in *.
assert (STEP : (if ranges_apart_pB bc sp wb k (elen w) (ELit 0%Z) lo (ELit (hi - lo)) then PKeep else PRepl []) = PKeep).
{ unfold ranges_apart_pB. cbn [elen]. rewrite Hne, Hsp, Hbr.
match goal with |- context [if ((?a <=? ?b) || (?c <=? ?d))%Z then _ else _] =>
replace ((a <=? b) || (c <=? d))%Z%bool with true; [reflexivity|];
symmetry; apply Bool.orb_true_iff; destruct Hnum as [H|H]; [left|right]; apply Z.leb_le; rewrite ?zlit64_idem; lia end. }
rewrite Hlt. destruct wb as [z| | | | | | |]; try exact STEP.
destruct z; try exact STEP. cbn in Hne. discriminate.
Qed.
Definition EINF (bc : bctx) (t : ntab) (K : kentry) (oi : option einfo) : Prop :=
match oi with
| None => kdescr K = None
| Some ei => kdescr K = Some (ei_kb ei, ei_k ei, ei_m ei)
/\ In (ei_kb ei, ei_bid ei) (nt_bucket t (bkey (ei_kb ei)))
/\ ei_br ei = base_rangeB bc (ei_kb ei)
end.
Lemma EINF_mono : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "Q6'R6'UK'XO';'RO%211'9%411'>'X<'L%3221&\3r1&UGr6r2%3221%63751r3%6251%93:51p041pmF<1pkLA1&Q8r5%24<18;r7r4%54241;p041p081pm<L1pQNQ01po>Q21po<Q31pi@Q51").
Proof. intros bc t t' K [ei|] Hm H; cbn [EINF] in *; [|exact H]. destruct H as (A & B & C). split; [exact A|]. split; [apply Hm; exact B| exact C]. Qed.
Lemma scan_entries_ok : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "R1'8'XO%211'UK'SB';'RO%211%811&Q:&UBr7%211r5%5221'E'>%129>%221>&V9r8%;11r6%442<1:(=r4r3%34CH21r2%54<I21%?3<71'Dr9%G11%I219'9%O11'X<'L%G221&\3r1&UG%12;?%43531%32Q2C%637B1p031pmF91pkL=1'\2&Q8%12CK%35QDQ>1Q1Q8%G251%H2E1p0J1p0Q;1pk2QF1po>QH1pkHQD1pk0QI1po<QK1pl:QM1pjDQN1").
Proof.
intros fk kn. induction kn as [|K rest IH]; intros t gs infos t' gs' HT H.
- cbn in H. injection H as <- <- <-. split; [exact HT|]. split; [intros; assumption|]. constructor.
- cbn [scan_entries] in H.
destruct (kdescr K) as [[[kb kk] om]|] eqn:HD.
+ destruct (intern (mkbc fk) t kb) as [[bid bi] t1] eqn:EI.
destruct (intern_ok _ _ _ _ _ _ HT EI) as (HT1 & Hbi & HIn & Hm1).
lazymatch type of H with (let '(_, _) := ?X in _) = _ => destruct X as [gid gs1] end.
destruct (scan_entries (mkbc fk) rest t1 _) as [[infos2 t2] gs2] eqn:ES.
injection H as <- <- <-.
destruct (IH _ _ _ _ _ HT1 ES) as (HT2 & Hm2 & HF).
split; [exact HT2|]. split; [intros k p Hp; apply Hm2; apply Hm1; exact Hp|].
constructor; [|exact HF]. cbn [EINF ei_kb ei_k ei_m ei_bid ei_br].
split; [exact HD|]. split; [apply Hm2; exact HIn|]. rewrite Hbi. reflexivity.
+ destruct (scan_entries (mkbc fk) rest t gs) as [[infos2 t2] gs2] eqn:ES.
injection H as <- <- <-.
destruct (IH _ _ _ _ _ HT ES) as (HT2 & Hm2 & HF).
split; [exact HT2|]. split; [exact Hm2|]. constructor; [exact HD | exact HF].
Qed.
Lemma chainKF_eq : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "R3'R6&SD'8'V>%211'XO';'X<%211'L'4pQP<21'>'K%2211%911&\3r1r6%33@21'E&W0r2r8%3221(A%63@21'UO&V2r:&VGr3%211&VE%113&VI%115&VH%117r7r5&VF%11;%311r4%A8@=;97621(Q;%K3D21p0F1p0N1po4Q?1%QA1Q>&R>&U<%12?Q4%36Q01?;HQ1&R=%16Q2Q7A=JQ3%Q63731p091piNQ=1pn>QB1pm>QF1pQNQJ1po:QL1pjJR01pi@R21").
Proof.
intros bc g sxs. induction sxs as [|sx rest IH]; intros K okb same_of br2 Hf; [reflexivity|].
cbn [mk_fl chainK2].
assert (IH' : chainKF bc (mk_fl g rest) K okb same_of br2 = chainK2 bc rest K okb same_of br2)
by (apply IH; intros; apply Hf; [right|]; assumption).
destruct (verdict sx g) eqn:Hv.
- rewrite (Hf sx (or_introl eq_refl) Hv). exact IH'.
- cbn [chainKF]. destruct (prune1pcK _ _ _ _ _ K _ br2); [exact IH'|reflexivity].
Qed.
Lemma verdict_inb_num : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "S1'V>&SD'RO'K'E'4&W0r4r3%3221(A%73621&SI%1265%:3914';%11=&RN%11;(2%12A<%A3531'D&\7&RKr5%211&VFr7%211%7241(6%L3K21'F'>%12Q0Q0%E11&[0&VGr;%211%411(=%14Q8Q8Q4Q3%I291%Q93941&RLr9%211r2r1%94Q@Q@21%Q12A1%QA3A51'H&\<&\:&WB&VE%11D%311%52QE1&\1&\>&VI%11J%311%511%<271&RM%11G%?2F1%A241%A2G3r8%C221%D2R5@%F221%H261%QI2J1%QJ2Q31qk:R>1%QA2R?1qlLR@1%QC2RA1qk8RB1%QE2RC1qlJRD1%QG2RE1%R32QI1p0R51p0R=1p0RA1pm0RJ1pj@RL1pjJRN1po4S01").
Proof.
intros sx [[b obr] [glo ghi]] ei m Hv Hi Hm. unfold verdict in Hv. unfold inb in Hi. rewrite Hm in Hi.
apply andb_prop in Hi as [Hi H4]. apply andb_prop in Hi as [Hi H3]. apply andb_prop in Hi as [H1 H2].
apply Pos.eqb_eq in H1. subst b. apply Z.leb_le in H3. apply Z.leb_le in H4.
destruct (Pos.eqb (ei_bid ei) (sx_bid sx)); [discriminate|]. split; [reflexivity|].
destruct (sp_rng (sx_sp sx)) as [[lo1 hi1]|]; [|discriminate].
destruct obr as [[lo2 hi2]|]; [|discriminate].
destruct (ei_br ei) as [[x2 y2]|]; [|discriminate]. cbn [obr_eqb] in H2. apply andb_prop in H2 as [X Y].
apply Z.eqb_eq in X. apply Z.eqb_eq in Y. subst x2 y2.
exists lo1, hi1, lo2, hi2. split; [reflexivity|]. split; [reflexivity|].
unfold sx_m1 in Hv. apply Bool.orb_prop in Hv. destruct Hv as [H|H]; apply Z.leb_le in H; lia.
Qed.
Lemma entriesG_eq : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "QH'8'XO%211'V>%411&SC';'RO%211%911'UK&Q:&UBr6%211r1%5221'I&Q=r7%811r2%4221%63D1:'\2&Q8r8%?11r3%4221r5r4%85OH321'E&S1r9%H11&U=%12C<%553=1J9&R?&J'ZM&V=%34Q921B%53:1Q0%=3Q<71p0?1p0I1p0Q11po@Q81pkHQ:1pl:QB1piHQ@1po:QB1pjDQE1").
Proof.
intros fk sxs bnds kn infos t1 HT HS HF. induction HF as [|K oi rest irest HK HF IH].
- cbn. clear. induction sxs as [|sx r IH]; [reflexivity|]. cbn. destruct (strip sx). exact IH.
- cbn [entriesG]. change (K :: rest) with ([K] ++ rest). rewrite chainRo_app, IH. f_equal.
rewrite <- (chain_slow_eq fk sxs [K] (Forall_SX_sp _ _ _ HS)).
pose proof (Forall_SX_sp _ _ _ HS) as HSP.
destruct oi as [ei|]; cbn [EINF] in HK.
+ destruct HK as (HD & HIn & Hbr).
assert (FULL : forall okb, okb = kbase K ->
chainK2 (mkbc fk) sxs K okb
(match okb with Some _ => Pos.eqb (ei_bid ei) | None => fun _ => false end)
(match okb with Some _ => ei_br ei | None => None end) = chain_slow (mkbc fk) sxs [K]).
{ intros okb Hokb. apply chainK2_eq; [exact HSP|exact Hokb|].
destruct okb as [kb|]; [|reflexivity].
destruct (kdescr_kbase _ _ _ _ HD) as [HB|(lo & hi & -> & _ & _)]; [|cbn in Hokb; discriminate].
rewrite <- Hokb in HB. injection HB as ->.
split; [exact Hbr|]. exact (Forall_SX_same _ _ _ _ _ HT HIn HS). }
unfold mk_gl. rewrite pt_get_map.
destruct (pt_get bnds (ei_gid ei)) as [g|]; [|apply FULL; reflexivity].
destruct (inb g ei) eqn:Hinb; [|apply FULL; reflexivity].
rewrite <- (FULL (kbase K) eq_refl). apply chainKF_eq.
intros sx Hsx Hv.
assert (Hm : exists m, ei_m ei = Some m).
{ unfold inb in Hinb. destruct (ei_m ei) as [m|]; [exists m; reflexivity|discriminate]. }
destruct Hm as [m Hm].
destruct (verdict_inb_num _ _ _ _ Hv Hinb Hm) as (Hne & lo1 & hi1 & lo2 & hi2 & Hsp & Hbr2 & Hnum).
pose proof (proj1 (Forall_forall _ _) HS sx Hsx) as (SXin & SXbr & SXsp).
rewrite Hm in HD.
destruct (kdescr_kbase _ _ _ _ HD) as [HB|(lo & hi & -> & Hkb & Hk)].
* rewrite HB. rewrite Hne. rewrite Hbr. eapply prune1pcK_keep_based; [exact HB|exact HD| |exact Hsp| | exact Hnum].
-- rewrite <- (nt_same_eq _ _ _ _ _ _ HT HIn SXin). exact Hne.
-- rewrite <- Hbr. exact Hbr2.
* cbn [kbase]. rewrite Hkb, Hk in *.
eapply prune1pcK_keep_img; [exact HD| |exact Hsp| rewrite <- Hbr; exact Hbr2 | exact Hnum].
rewrite <- (nt_same_eq _ _ _ _ _ _ HT HIn SXin). exact Hne.
+ apply chainK2_eq; [exact HSP| symmetry; apply kdescr_None_kbase; exact HK | reflexivity].
Qed.
Lemma carryG_eq : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "I'8'ZM%211'XO%411'E&R:&UB&XAr1%211%411r2%73214&3&Q<&\6%12@5%3281&R?%13:3;%73B31%A3B91pl:C1plNF1").
Proof.
intros log kn. unfold carryG.
destruct (mk_stxs (mkbc (facts_of kn)) log nt_empty) as [sxs t0] eqn:E.
destruct (mk_stxs_ok _ _ _ _ _ (NTI_empty _) E) as (HT0 & HS0 & Hmap & _).
destruct (scan_entries (mkbc (facts_of kn)) kn t0 gst_empty) as [[infos t1] gs] eqn:ES.
destruct (scan_entries_ok _ _ _ _ _ _ _ HT0 ES) as (HT1 & Hm & HF).
assert (HS1 : Forall (SX_OK (mkbc (facts_of kn)) t1) sxs).
{ apply Forall_impl with (P := SX_OK (mkbc (facts_of kn)) t0); [|exact HS0]. intros sx. apply SX_OK_mono. exact Hm. }
rewrite (stores_part_eq _ _ _ HT0 HS0), (entriesG_eq _ _ _ _ _ _ HT1 HS1 HF), Hmap. reflexivity.
Qed.
Definition carryK (bc : bctx) (log : list sentry) (kn : list kentry) (hints : list bool)
: list kentry * list sidecond * list bool :=
match log, hints with
| [], _ => (kn, [], hints)
| _, [] => (carryG bc log kn, [], [])
| _, _ => carryB bc log kn hints
end.
Lemma carryK_eq : ltac2:(TCodec.tc2 tcn__AxSymExec3BK "L'8'ZM%211'XO%411'4%611'E'>'ZO%:11%3271%4216&R;&UB&XAr2%211%411r3r1%843251&WK%13473%A3<31pk<C1pl:F1plNI1").
Proof.
intros log kn hints. unfold carryK. destruct log as [|s older]; [reflexivity|].
destruct hints as [|h hs]; [|apply carryB_eq].
rewrite carry_vertical, carryG_eq. reflexivity.
Qed.
End AX2BK.
