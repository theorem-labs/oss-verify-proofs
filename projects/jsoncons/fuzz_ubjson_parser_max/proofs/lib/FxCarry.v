(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool FunctionalExtensionality.
From Stdlib Require Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec AxSymExec3 AxSymExec3B AsanPlanCore.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import FxBlock.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__FxCarry () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Peano."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "Corelib.Numbers.Cyclic.Int63.PrimInt63."; "Corelib.Numbers.Cyclic.Int63.Uint63Axioms."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AxSymExec3.AX2."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AxSymExec3B.AX2B."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.FxCarry.CARF."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.FxCarry.CARF.GrpKeep."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.FxCarry.CARF.P2Q."; "Stdlib.Lists.List."; "Stdlib.PArith.BinPos.Pos."; "Stdlib.ZArith.BinInt.Z."], [["0A"; "0A0"; "0B"; "0B0"; "0C"; "1None"; "1Some"; "1andb"; "1bool"; "1cons"; "1false"; "1fst"; "1list"; "1nat"; "1nil"; "1option"]; ["1option_map"; "1orb"; "1pair"; "1prod"; "1snd"; "1true"; "2and"; "2eq"; "2ex"; "2not"; "2or"; "3le"; "4Forall"; "4map"; "5Z"; "5Zpos"]; ["5positive"; "6add"; "6int"; "6leb"; "6lsl"; "6ltb"; "6mul"; "6sub"; "7to_Z"; "7wB"; "0D"; "0G"; "0J"; "0K"; "0K'"; "0M"]; ["0N"; "0R"; "8ELit"; "8KDisj"; "8KWord"; "8SA"; "8SE"; "8a_base"; "8a_off"; "8elen"; "8expr"; "8kbase"; "8kentry"; "8ktrim"; "8lin"; "8lin_of"]; ["8lin_range"; "8lsub_e"; "8mtwo63z"; "8pt_get"; "8ptree"; "8saddr"; "8sentry"; "8sidecond"; "8snorm"; "8sp_D"; "8sp_Dx"; "8sp_rng"; "8sprep"; "8two63z"; "8two64"; "8xt_const"]; ["8xt_lin"; "8xterms"; "8zlit64"; "8zmod64"; "9BI"; "9EINF"; "9NTI"; "9PKeep"; "9PRepl"; "9SX_OK"; "9alookupE"; "9base_rangeB"; "9bc_fk"; "9bctx"; "9binfo"; "9bkey"]; ["9carryG"; "9carryK"; "9chainK2"; "9chainKF"; "9chain_slow"; "9disj_sidesB"; "9disj_sides_xB"; "9einfo"; "9entriesG"; "9erangeB"; "9g1cB"; "9gs_bnds"; "9gs_gid"; "9gs_next"; "9gst"; "9gst_empty"]; ["9gtab"; "9gval"; "9in_sidesB"; "9in_sides_xB"; "9intern"; "9kdescr"; "9lin_apartB"; "9lin_ge0B"; "9lin_ge0_scaledB"; "9lin_nowrapRB"; "9lin_testB"; "9mk_fl"; "9mk_gl"; "9mk_sprepB"; "9mk_stxs"; "9nt_bucket"]; ["9nt_info"; "9ntab"; "9obr_eqb"; "9pk_list"; "9pk_res"; "9prune1pB"; "9prune1pcB"; "9prune1pcK"; "9ranges_apart_pcB"; "9scan_entries"; "9stores_part"; "9stx"; "9sub_itvB"; "9sub_itv_xB"; "9sx_a"; "9sx_bid"]; ["9sx_br"; "9sx_m1"; "9sx_sp"; "9sx_v"; "9sx_w"; "9verdict"; "9xinside0B"; "9xinsideB"; "9xinside_numB"; "9xt_nowrapB"; ":B59"; ":BOK"; ":BXOK"; ":EINFF"; ":GMEMO"; ":GSI"]; [";prG"; ":IXE_OK"; ":IXL_OK"; ":LB"; ":LG"; ":MEMO_OK"; ":MEMO_OKX"; ":MOK"; ":NOK"; "<p2iQ4"; "<pfin"; ":PREM"; ":PRE_OK"; ":SBL_OK"; ":SubG"; ":WCOK"]; [":WTOK"; ":XOK"; ":alookupEF"; ":be_kd"; ":bext"; ":binf"; ":bmemo"; ":bnd_addF"; ":bx"; ":bx_get"; ":carryGF"; ":carryGF8C"; ":carryGF9C"; ":carryKF"; ":carryKF1"; ":carryKF_ctx"]; [":chainK2F"; ":chainK2F2"; ":chainKFF"; ":chainKFF2"; ":chainKI"; ":chainKP"; ":chain_slowF"; ":disj_both"; ":disj_bothW"; ":ef_ei"; ":ei_strip"; ":einfoF"; ":enj_of"; ":entC"; ":ent_iv"; ":entriesGF"]; [":entriesGF8"; ":fastkeep"; ":forallbF"; ":g1cBF"; ":g1cF"; ":ge0P"; ":ggroupK"; ":ggroup_c"; ":gkeyI"; ":gmono"; ":gp"; ":gp_dead"; ":gq_of"; ":gqj_of"; ":gxi"; ":hull"]; [":hull_of"; ":hv_other"; ":i0"; ":i1"; ":i16"; ":i4"; ":imax"; ":imin"; ":in_grpo"; ":in_sidesM"; ":in_sidesXM"; ":in_sides_num"; ":internF"; ":intern_c"; ":intern_r"; ":is_fact_entry"]; [":is_kdisjb"; ":iv_of"; ":ix_add"; ":ix_cands"; ":ix_find"; ":ix_ins"; ":ix_upd"; ":ixb"; ":ixb_b"; ":ixb_ok"; ":ixb_t"; ":kdescrF"; ":ksym"; ":linV"; ":linV2"; ":linV2M"]; [":lin_apartF"; ":lin_lo"; ":lin_loM"; ":lin_rangeM"; ":m61"; ":mk_abj"; ":mk_bext"; ":mk_binf"; ":mk_flF"; ":mk_flG"; ":mk_flM"; ":mk_glF"; ":mk_glF6"; ":mk_gp"; ":mk_gpM"; ":mk_pre"]; [":mk_rows"; ":mk_rowsM"; ":mk_sbl"; ":mk_sctx"; ":mk_sctxW"; ":mk_sctx_c"; ":mk_sctx_c1"; ":mk_sidet"; ":mk_sidetM"; ":mk_sprepF"; ":mk_stxsC2"; ":mk_stxsC3"; ":mk_stxsF"; ":mk_stxsR"; ":mk_sxi"; ":mk_wtab"]; [":mk_wtabM"; ":mk_xin"; ":mk_xinM"; ":narrow"; ":nm_get"; ":nmemo"; ":nonov"; ":notouch"; ":nov"; ":num_sub"; ":num_subW"; ":ok_lo"; ":omax"; ":osame"; ":oshift"; ":p2iS"]; [":pk_rel"; ":prune1pBF"; ":prune1pcBF"; ":prune1pcKF"; ":prune1pcKF2"; ":prune1pcKF2'"; ":prune1pcKF3"; ":prune1pcKS"; ":prune1pcKX"; ":ranges_apart_pcF"; ":rm_find"; ":rm_get"; ":rmemo"; ":rng2l"; ":sb_find"; ":sb_pop"]; [":sbe"; ":sbe_b"; ":sbe_h"; ":sbkey"; ":sbucket"; ":scanF"; ":scanF2"; ":sd_dead"; ":sfl"; ":sgran"; ":si_abj"; ":si_iv"; ":si_sx"; ":sidet"; ":skipo5"; ":skipv5"]; [":sm_find"; ":smemo"; ":sp9"; ":ssvJ"; ":stores_partF"; ":stores_partF2"; ":stores_partF5"; ":stores_partF9"; ":stores_partX"; ":sxi"; ":symnumJ"; ":verdictF"; ":verdictJ"; ":wc_empty"; ":wc_find"; ":wcache"]; [":wlenF"; ":wrow"; ":wt_empty"; ":wtab"; ":wtabs"; ":xeval"; ":xget"; ":xin"; ":z2b"; ":z2i"; ":z2l"; ":zlit64F"; "0S"; "=Forall2"; "=In"; "=filter"]; ["=rev"; ">eqb"; ">size_nat"; "?add"; "?div"; "?le"; "?leb"; "?lt"; "?ltb"; "?modulo"; "?mul"; "?of_nat"; "?opp"; "?pow"; "?sub"; "0T1"]; ["0T2"; "0X"; "0a"; "0acc"; "0ai"; "0all"; "0b"; "0b'"; "0b1"; "0b2"; "0bc"; "0bi"; "0bid"; "0bnds"; "0br2"; "0bs"]; ["0bt"; "0c"; "0c'"; "0c0"; "0c1"; "0c2"; "0cands"; "0cb"; "0co"; "0d"; "0d0"; "0e"; "0e0"; "0ex"; "0f"; "0fl"]; ["0g"; "0ghi"; "0gid"; "0gk"; "0glo"; "0gq"; "0gqj"; "0gs"; "0gs'"; "0gs0"; "0gs1"; "0gs2"; "0gx"; "0h"; "0hi"; "0hi1"]; ["0hints"; "0i"; "0i1"; "0i2"; "0id"; "0info"; "0infos"; "0infos1"; "0infos2"; "0j"; "0k"; "0k'"; "0k1"; "0k2"; "0k2'"; "0kb"]; ["0kd"; "0kk"; "0kk'"; "0kn"; "0ks"; "0kt"; "0l"; "0l0"; "0lb"; "0lg"; "0lh"; "0lo"; "0lo1"; "0log"; "0m"; "0m'"]; ["0m1"; "0m2"; "0mk"; "0n"; "0n'"; "0n1"; "0n2"; "0n2'"; "0neg"; "0neg'"; "0newer"; "0ns"; "0nt"; "0o"; "0obr"; "0okb"]; ["0p"; "0pos"; "0pos'"; "0pre"; "0pw"; "0r"; "0rng"; "0s"; "0same"; "0same_of"; "0sbl"; "0scs"; "0se"; "0si"; "0sis"; "0skip"]; ["0skip1"; "0skip2"; "0sp"; "0sx"; "0sxs"; "0t"; "0t'"; "0t1"; "0t2"; "0ts"; "0tt"; "0v"; "0w"; "0wa"; "0wv"; "0x"]; ["0xo"; "0y"; "0z"; "0z1"; "0z2'"; "0zh"]]).
Module CARF.
Import AX2. Import AX2B.
Notation expr_eqbF := BLKF.expr_eqbF.
Ltac eF := rewrite ?BLKF.expr_eqbF_eq in *.
Definition is_kdisjb (K : kentry) : bool := match K with KDisj _ _ _ _ => true | _ => false end.
Definition is_kwrb (K : kentry) : bool := match K with KWr _ _ => true | _ => false end.
Record bext := BE { be_kd : list kentry; be_kw : list kentry }.
Definition mk_bext (bc : bctx) : bext := BE (List.filter is_kdisjb (bc_fk bc)) (List.filter is_kwrb (bc_fk bc)).
Local Open Scope Z_scope.
Fixpoint existsbF {T : Type} (f : T -> bool) (l : list T) : bool :=
match l with [] => false | x :: r => if f x then true else existsbF f r end.
Record bx := BX { bx_b : expr; bx_l : lin; bx_nw : bool }.
Definition mk_bx (bc : bctx) (b : expr) : bx := BX b (lin_of b) (lin_nowrapRB bc b).
Definition bx_get (bc : bctx) (o : option bx) (b : expr) : lin * bool :=
match o with
| Some x => if expr_eqbF (bx_b x) b then (bx_l x, bx_nw x) else (lin_of b, lin_nowrapRB bc b)
| None => (lin_of b, lin_nowrapRB bc b)
end.
Definition lin_apartF (bc : bctx) (i1 i2 : option bx) (b1 : expr) (k1 n1 : Z) (b2 : expr) (k2 n2 : Z) : bool :=
if shares_var b1 b2 then
let '(l1, nw1) := bx_get bc i1 b1 in
if nw1 then
let '(l2, nw2) := bx_get bc i2 b2 in
if nw2 then lin_testB bc (fst l2 + k2 - fst l1 - k1) (lsub_e (snd l2) (snd l1)) (fun lo hi => if Z.leb n1 lo then true else Z.leb hi (- n2))
else false
else false
else false.
Definition ranges_apart_pcF (bc : bctx) (i1 i2 : option bx) (sp : sprep) (b1 : expr) (k1 : Z) (n1 : expr)
(br2 : option (Z * Z)) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
match n1, n2 with
| ELit z1, ELit z2 =>
let m1 := zlit64 z1 in let m2 := zlit64 z2 in
if (match sp_rng sp, br2 with
| Some (lo1, hi1), Some (lo2, hi2) =>
if Z.leb (hi1 + k1 + m1) (lo2 + k2) then true else Z.leb (hi2 + k2 + m2) (lo1 + k1)
| _, _ => false
end) then true
else if lin_apartF bc i1 i2 b1 k1 m1 b2 k2 m2 then true
else in_sidesB bc (sp_D sp) b2 k2 m2
| _, _ => ranges_apart_pcB bc sp b1 k1 n1 br2 b2 k2 n2
end.
Definition prune1pcKF (bc : bctx) (i1 i2 : option bx) (sp : sprep) (wa : saddr) (w : nat) (wv : expr) (K : kentry) (same : bool)
(br2 : option (Z * Z)) : pk_res :=
let k := a_off wa in
let wb := a_base wa in
let zfK (mk : saddr -> expr -> kentry) (kb : expr) (kk : Z) (len : expr) :=
if same then
match len with
| ELit l0 => PRepl (ktrim mk kb kk l0 k w)
| _ => if Z.leb (k + Z.of_nat w) kk then PKeep else PRepl (kcutB bc mk wb k (elen w) kb kk len)
end
else if ranges_apart_pcF bc i1 i2 sp wb k (elen w) br2 kb kk len then PKeep
else PRepl (kcutB bc mk wb k (elen w) kb kk len) in
match K with
| KAlign _ _ | KRange _ _ _ | KWr _ _ | KDisj _ _ _ _ => PKeep
| KImg lo hi =>
match wb with
| ELit 0 =>
let r1 := if Z.ltb lo (Z.min k hi) then [KImg lo (Z.min k hi)] else [] in
let lo2 := Z.max lo (k + Z.of_nat w) in
let r2 := if Z.ltb lo2 hi then [KImg lo2 hi] else [] in
PRepl (r1 ++ r2)
| _ => if Z.ltb (hi - lo) two64 then
(if ranges_apart_pB bc sp wb k (elen w) (ELit 0) lo (ELit (hi - lo)) then PKeep else PRepl [])
else PRepl []
end
| KZero (SA kb kk) len => zfK KZero kb kk len
| KFill (SA kb kk) len c => zfK (fun a n => KFill a n c) kb kk len
| KUnk (SA kb kk) len => zfK KUnk kb kk len
| KWord (SA kb kk) w' v =>
if same then (if Z.leb (kk + Z.of_nat w') k then PKeep else if Z.leb (k + Z.of_nat w) kk then PKeep else PRepl (kword_cut kb kk w' v k w))
else if ranges_apart_pcF bc i1 i2 sp wb k (elen w) br2 kb kk (elen w') then PKeep
else if (if Nat.eqb w 1 then if Nat.eqb w' 1 then expr_eqb wv v else false else false) then PKeep
else PRepl []
| KBlob (SA kb kk) len bk =>
if same then
match len with
| ELit l0 => let l := zmod64 l0 in
if Z.leb (kk + l) k then PKeep else if Z.leb (k + Z.of_nat w) kk then PKeep else PRepl []
| _ => if Z.leb (k + Z.of_nat w) kk then PKeep else PRepl []
end
else if ranges_apart_pcF bc i1 i2 sp wb k (elen w) br2 kb kk len then PKeep else PRepl []
end.
Definition prune1pBF (bc : bctx) (sp : sprep) (wa : saddr) (w : nat) (wv : expr) (K : kentry) (hints : list bool)
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
| _ => if Z.ltb (hi - lo) two64 then diffbase (SA (ELit 0) lo) (ELit (hi - lo))
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
let l := zmod64 l0 in
(if (Z.leb (kk + l) k || Z.leb (k + Z.of_nat w) kk)%bool
then ([K], [], hints) else ([], [], hints))
| _ => if Z.leb (k + Z.of_nat w) kk then ([K], [], hints) else ([], [], hints)
end
else diffbase (SA kb kk) len
end.
Definition prune1pcBF (bc : bctx) (sp : sprep) (wa : saddr) (w : nat) (wv : expr) (K : kentry) (hints : list bool)
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
| KAlign _ _ | KRange _ _ _ | KWr _ _ | KDisj _ _ _ _ | KImg _ _ => prune1pBF bc sp wa w wv K hints
| KZero (SA kb kk) len =>
if expr_eqb kb (a_base wa) then prune1pBF bc sp wa w wv K hints
else if ranges_apart_pcB bc sp (a_base wa) k (elen w) br2 kb kk len then ([K], [], hints)
else match kzero_cutB bc (a_base wa) k (elen w) kb kk len with
| [] => diffbase (SA kb kk) len
| cut => (cut, [], hints)
end
| KFill (SA kb kk) len c =>
if expr_eqb kb (a_base wa) then prune1pBF bc sp wa w wv K hints
else if ranges_apart_pcB bc sp (a_base wa) k (elen w) br2 kb kk len then ([K], [], hints)
else match kfill_cutB bc c (a_base wa) k (elen w) kb kk len with
| [] => diffbase (SA kb kk) len
| cut => (cut, [], hints)
end
| KUnk (SA kb kk) len =>
if expr_eqb kb (a_base wa) then prune1pBF bc sp wa w wv K hints
else if ranges_apart_pcB bc sp (a_base wa) k (elen w) br2 kb kk len then ([K], [], hints)
else match kunk_cutB bc (a_base wa) k (elen w) kb kk len with
| [] => diffbase (SA kb kk) len
| cut => (cut, [], hints)
end
| KWord (SA kb kk) w' v =>
if expr_eqb kb (a_base wa) then prune1pBF bc sp wa w wv K hints
else if ranges_apart_pcB bc sp (a_base wa) k (elen w) br2 kb kk (elen w') then ([K], [], hints)
else if (Nat.eqb w 1 && Nat.eqb w' 1 && expr_eqb wv v)%bool
then ([K], [], hints)
else diffbase (SA kb kk) (elen w')
| KBlob (SA kb kk) len bk =>
if expr_eqb kb (a_base wa) then prune1pBF bc sp wa w wv K hints
else diffbase (SA kb kk) len
end.
Definition g1cBF (bc : bctx) (sx : stx) (K : kentry) : list kentry :=
fst (fst (prune1pcBF bc (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) K [] (obrB bc K))).
Definition i0 : PrimInt63.int := Uint63.of_Z 0.
Definition i1 : PrimInt63.int := Uint63.of_Z 1.
Definition m61 : PrimInt63.int := Uint63.of_Z (2 ^ 61).
Definition B59 : PrimInt63.int := Uint63.of_Z (2 ^ 59).
Fixpoint p2iS (p : positive) (acc pw : PrimInt63.int) : option PrimInt63.int :=
if PrimInt63.ltb m61 pw then None else
match p with
| xH => Some (PrimInt63.add acc pw)
| xO q => p2iS q acc (PrimInt63.add pw pw)
| xI q => p2iS q (PrimInt63.add acc pw) (PrimInt63.add pw pw)
end.
Module P2Q.
Import PrimInt63.
Local Notation toZ := Uint63Axioms.to_Z.
Lemma m61_val : ltac2:(TCodec.tc2 tcn__FxCarry ":'G'N&Q8&X4%211&[M+2+QM%3221%93851"). Proof. reflexivity. Qed.
Lemma wB_val : ltac2:(TCodec.tc2 tcn__FxCarry "8'G'N&Q9&[M+2+QO%3221%73651"). Proof. reflexivity. Qed.
Definition pfin (pw r : PrimInt63.int) : option PrimInt63.int :=
if PrimInt63.ltb 0%uint63 pw then (if PrimInt63.leb pw m61 then Some r else None) else None.
Fixpoint p2iQ4 (p : positive) (acc pw : PrimInt63.int) : option PrimInt63.int :=
match p with
| xH => pfin pw (PrimInt63.add acc pw)
| xO q1 =>
match q1 with
| xH => pfin (PrimInt63.lsl pw 1%uint63) (PrimInt63.add acc (PrimInt63.mul pw 2%uint63))
| xO q2 =>
match q2 with
| xH => pfin (PrimInt63.lsl pw 2%uint63) (PrimInt63.add acc (PrimInt63.mul pw 4%uint63))
| xO q3 =>
match q3 with
| xH => pfin (PrimInt63.lsl pw 3%uint63) (PrimInt63.add acc (PrimInt63.mul pw 8%uint63))
| xO q4 =>
p2iQ4 q4 acc (PrimInt63.lsl pw 4%uint63)
| xI q4 =>
p2iQ4 q4 (PrimInt63.add acc (PrimInt63.mul pw 8%uint63)) (PrimInt63.lsl pw 4%uint63)
end
| xI q3 =>
match q3 with
| xH => pfin (PrimInt63.lsl pw 3%uint63) (PrimInt63.add acc (PrimInt63.mul pw 12%uint63))
| xO q4 =>
p2iQ4 q4 (PrimInt63.add acc (PrimInt63.mul pw 4%uint63)) (PrimInt63.lsl pw 4%uint63)
| xI q4 =>
p2iQ4 q4 (PrimInt63.add acc (PrimInt63.mul pw 12%uint63)) (PrimInt63.lsl pw 4%uint63)
end
end
| xI q2 =>
match q2 with
| xH => pfin (PrimInt63.lsl pw 2%uint63) (PrimInt63.add acc (PrimInt63.mul pw 6%uint63))
| xO q3 =>
match q3 with
| xH => pfin (PrimInt63.lsl pw 3%uint63) (PrimInt63.add acc (PrimInt63.mul pw 10%uint63))
| xO q4 =>
p2iQ4 q4 (PrimInt63.add acc (PrimInt63.mul pw 2%uint63)) (PrimInt63.lsl pw 4%uint63)
| xI q4 =>
p2iQ4 q4 (PrimInt63.add acc (PrimInt63.mul pw 10%uint63)) (PrimInt63.lsl pw 4%uint63)
end
| xI q3 =>
match q3 with
| xH => pfin (PrimInt63.lsl pw 3%uint63) (PrimInt63.add acc (PrimInt63.mul pw 14%uint63))
| xO q4 =>
p2iQ4 q4 (PrimInt63.add acc (PrimInt63.mul pw 6%uint63)) (PrimInt63.lsl pw 4%uint63)
| xI q4 =>
p2iQ4 q4 (PrimInt63.add acc (PrimInt63.mul pw 14%uint63)) (PrimInt63.lsl pw 4%uint63)
end
end
end
| xI q1 =>
match q1 with
| xH => pfin (PrimInt63.lsl pw 1%uint63) (PrimInt63.add acc (PrimInt63.mul pw 3%uint63))
| xO q2 =>
match q2 with
| xH => pfin (PrimInt63.lsl pw 2%uint63) (PrimInt63.add acc (PrimInt63.mul pw 5%uint63))
| xO q3 =>
match q3 with
| xH => pfin (PrimInt63.lsl pw 3%uint63) (PrimInt63.add acc (PrimInt63.mul pw 9%uint63))
| xO q4 =>
p2iQ4 q4 (PrimInt63.add acc pw) (PrimInt63.lsl pw 4%uint63)
| xI q4 =>
p2iQ4 q4 (PrimInt63.add acc (PrimInt63.mul pw 9%uint63)) (PrimInt63.lsl pw 4%uint63)
end
| xI q3 =>
match q3 with
| xH => pfin (PrimInt63.lsl pw 3%uint63) (PrimInt63.add acc (PrimInt63.mul pw 13%uint63))
| xO q4 =>
p2iQ4 q4 (PrimInt63.add acc (PrimInt63.mul pw 5%uint63)) (PrimInt63.lsl pw 4%uint63)
| xI q4 =>
p2iQ4 q4 (PrimInt63.add acc (PrimInt63.mul pw 13%uint63)) (PrimInt63.lsl pw 4%uint63)
end
end
| xI q2 =>
match q2 with
| xH => pfin (PrimInt63.lsl pw 2%uint63) (PrimInt63.add acc (PrimInt63.mul pw 7%uint63))
| xO q3 =>
match q3 with
| xH => pfin (PrimInt63.lsl pw 3%uint63) (PrimInt63.add acc (PrimInt63.mul pw 11%uint63))
| xO q4 =>
p2iQ4 q4 (PrimInt63.add acc (PrimInt63.mul pw 3%uint63)) (PrimInt63.lsl pw 4%uint63)
| xI q4 =>
p2iQ4 q4 (PrimInt63.add acc (PrimInt63.mul pw 11%uint63)) (PrimInt63.lsl pw 4%uint63)
end
| xI q3 =>
match q3 with
| xH => pfin (PrimInt63.lsl pw 3%uint63) (PrimInt63.add acc (PrimInt63.mul pw 15%uint63))
| xO q4 =>
p2iQ4 q4 (PrimInt63.add acc (PrimInt63.mul pw 7%uint63)) (PrimInt63.lsl pw 4%uint63)
| xI q4 =>
p2iQ4 q4 (PrimInt63.add acc (PrimInt63.mul pw 15%uint63)) (PrimInt63.lsl pw 4%uint63)
end
end
end
end.
Lemma pow2_mod_pos : ltac2:(TCodec.tc2 tcn__FxCarry "D'N&[Ezr1%3221&[G&[I&[M+2r2%3221+QO%5241%7231%92<1r3%;215p031p0>1po<C1").
Proof.
intros t Ht H. destruct (Z.lt_ge_cases t 63) as [L|G]; [exact L|exfalso].
replace t with (63 + (t - 63)) in H by lia. rewrite Z.pow_add_r in H by lia.
rewrite Z.mul_comm, Z.mod_mul in H by lia. lia.
Qed.
Lemma pfin_spec : ltac2:(TCodec.tc2 tcn__FxCarry "QJ&Q2'N&[Ezr2%3221'G&Q8r6%211&[I&[M+2r3%3221+QO%5241%7231%<3A91%9263%>3C;1'Fr4%E2D1&[G&[Cr5+1%3221%B2A1%6281%:281'?%11Q1&U:r9r8%3221(6r7%22Q81%Q33841%Q316%Q53Q:1Q3+QN%Q22Q11%F2Q61%J241p071p0B1p0N1p0Q11p0Q?1p2QD1pn@QE1pQP0QG1pn<QH1pn:QI1").
Proof.
intros pw r x s A Hs Hpw Hr HA H. unfold pfin in H.
destruct (PrimInt63.ltb _ pw) eqn:E1; [|discriminate]. destruct (PrimInt63.leb pw m61) eqn:E2; [|discriminate].
injection H as <-. apply Uint63Axioms.ltb_spec in E1. apply Uint63Axioms.leb_spec in E2. rewrite m61_val in E2.
change (toZ 0%uint63) with 0 in E1. rewrite Hpw in E1, E2.
pose proof (pow2_mod_pos s Hs E1) as L. rewrite Z.mod_small in E2 by (split; [apply Z.pow_nonneg; lia|apply Z.pow_lt_mono_r; lia]).
assert (s <= 61) by (apply (Z.pow_le_mono_r_iff 2); lia).
assert (2 ^ (s + 1) <= 2 ^ 62) by (apply Z.pow_le_mono_r; lia).
rewrite Hr, Z.mod_small by lia. lia.
Qed.
Lemma lsl_inv : ltac2:(TCodec.tc2 tcn__FxCarry "Q9&Q2'N&[Ezr3%3221'G&Q8r5%211&[I&[M+2r4%3221+QO%5241%7231%<3A91%<16%>3C1@%C2B8&Q4r8r6%3221%C11&[Cr7%221E%C2B1%E21?%J3O61p0<1p0>1p0A1p0O1pRJQ41pkDQ61pn@Q61pn:Q81").
Proof.
intros pw s j J Hs Hpw Hj HJ. rewrite Uint63Axioms.lsl_spec, wB_val, Hpw, Hj, Z.mul_mod_idemp_l by lia.
rewrite Z.pow_add_r by lia. reflexivity.
Qed.
Lemma addmul_inv : ltac2:(TCodec.tc2 tcn__FxCarry "Q>&Q2'N'G&Q8r5%211&[I&[M+2r3%3221+QO%5241%7231%<3=91r7%=11%;285%@3A21r6%A11%C3D1<&Q1r9&Q6r8%221;%5241%I11&[C&[J%H2G<r4%3221%52N1%M21G%Q23Q381p0@1p0D1p0I1p:Q71p2Q81pn@Q91pi4Q;1pn:Q<1ph8Q=1").
Proof.
intros acc pw c s A C Hpw Ha Hc. rewrite Uint63Axioms.add_spec, Uint63Axioms.mul_spec, wB_val, Hpw, Ha, Hc.
rewrite Z.mul_mod_idemp_l, Z.add_mod_idemp_l, Z.add_mod_idemp_r by lia. reflexivity.
Qed.
Lemma add_inv : ltac2:(TCodec.tc2 tcn__FxCarry "Q6&Q2'N'G&Q8r3%211&[I&[M+2r2%3221+QO%5241%7231%<3=91r5%=11%;285%@3A21&Q1r6%2216%C11&[C&[Jr4%C2B1+1%4221%62I1%H21B%M3N91p0>1p0C1p2Q11pn@Q21pn:Q41ph8Q51").
Proof.
intros acc pw s A Hpw Ha. rewrite Uint63Axioms.add_spec, wB_val, Hpw, Ha.
rewrite Z.add_mod_idemp_l, Z.add_mod_idemp_r, Z.mul_1_r by lia. reflexivity.
Qed.
Lemma acc_inv0 : ltac2:(TCodec.tc2 tcn__FxCarry "M&Q2'N'G&Q8r3%211&[Ir1&[M+2+QO%3221%6251%;3<81r4%<11&[Cr2&[J%;2:?z%3221%6251%A21<%F3G91p0<1p2I1pn@J1ph8L1").
Proof. intros acc s A H. rewrite Z.mul_0_r, Z.add_0_r. exact H. Qed.
Ltac posfacts p := lazymatch p with
| xI ?q => pose proof (Pos2Z.inj_xI q); posfacts q
| xO ?q => pose proof (Pos2Z.inj_xO q); posfacts q
| _ => idtac end.
Lemma p2iQ4_spec : ltac2:(TCodec.tc2 tcn__FxCarry "R:'='Q0&Q2'N'K&[Br6%211r7%5221&[Ezr3%3221'G&Q8%11:&[I&[M+2r4%3221+QO%5241%7231%;3F91r8%<11%;285%?3J21'Fr5%F2E1&[G%@2?L%2241%6241'?%11Q4&U9r;r:r9%43321(6%12Q;C%Q03831%Q015&[C&[J%Q02OH(Or<%211%5241%72Q?1%Q:3QE91+QN%Q82Q71%J241%N241p0?1p0J1p0Q21p0Q71p0QD1p0QI1p2R01pn@R11pn<R31pn:R41ph8R51pn2R71pm8R91").
Proof.
induction n as [|n IH]; intros p acc pw r s A Hn Hs Hpw Ha HA H; [destruct p; cbn in Hn; lia|].
assert (P0 : 0 < 2 ^ s) by (apply Z.pow_pos_nonneg; lia).
destruct p as [[[[q|q|]|[q|q|]|]|[[q|q|]|[q|q|]|]|]|[[[q|q|]|[q|q|]|]|[[q|q|]|[q|q|]|]|]|]; cbn [p2iQ4] in H;
lazymatch type of H with
| p2iQ4 ?q ?acc' (PrimInt63.lsl _ ?j) = _ =>
let C := lazymatch acc' with
| PrimInt63.add _ (PrimInt63.mul _ ?c) => eval vm_compute in (toZ c)
| PrimInt63.add _ _ => constr:(1)
| _ => constr:(0)
end in
let Hacc := lazymatch acc' with
| PrimInt63.add _ (PrimInt63.mul _ ?c) => constr:(addmul_inv acc pw c s A C Hpw Ha eq_refl)
| PrimInt63.add _ _ => constr:(add_inv acc pw s A Hpw Ha)
| _ => constr:(acc_inv0 acc s A Ha)
end in
assert (Hn' : (Pos.size_nat q <= n)%nat) by (cbn [Pos.size_nat] in Hn; lia);
pose proof (IH q acc' _ r (s + 4) (A + 2 ^ s * C) Hn' ltac:(lia) (lsl_inv pw s j 4 Hs Hpw eq_refl ltac:(lia)) Hacc) as R;
rewrite Z.pow_add_r in R by lia; change (2 ^ 4) with 16 in R;
assert (HA' : 0 <= A + 2 ^ s * C < 2 ^ s * 16) by lia;
specialize (R HA' H); destruct R as [R1 R2];
lazymatch goal with |- _ = _ + _ * Z.pos ?p /\ _ =>
posfacts p;
assert (E : Z.pos p = 16 * Z.pos q + C) by lia; rewrite E
end;
(split; [rewrite R1; ring|eapply Z.le_lt_trans; [|exact R2]; apply Z.eq_le_incl; ring])
| pfin pw (PrimInt63.add acc pw) = _ =>
exact (pfin_spec pw _ r s (A + 2 ^ s * 1) Hs Hpw (add_inv acc pw s A Hpw Ha) ltac:(rewrite Z.pow_add_r by lia; change (2 ^ 1) with 2; lia) H)
| pfin (PrimInt63.lsl pw ?j) (PrimInt63.add acc (PrimInt63.mul pw ?c)) = _ =>
let J := eval vm_compute in (toZ j) in
let C := eval vm_compute in (toZ c) in
let T := eval vm_compute in (2 ^ (J + 1)) in
lazymatch goal with |- _ = _ + _ * Z.pos ?p /\ _ => change (Z.pos p) with C end;
refine (pfin_spec (PrimInt63.lsl pw j) _ r (s + J) (A + 2 ^ s * C) ltac:(lia) (lsl_inv pw s j J Hs Hpw eq_refl ltac:(lia)) (addmul_inv acc pw c s A C Hpw Ha eq_refl) _ H);
replace (s + J + 1) with (s + (J + 1)) by ring; rewrite Z.pow_add_r by lia; change (2 ^ (J + 1)) with T; lia
end.
Qed.
Lemma p2iQ4_val : ltac2:(TCodec.tc2 tcn__FxCarry "Q0'Q0&Q2'G'?%113&U9r2&W2&W3%43321(6r1%22;1%;3941'F'N&Q8%11;(Or3%211%C3641&[G&[M+2+QN%3221%5271%>271p0@1pn<M1pn2O1").
Proof.
intros p r H. pose proof (p2iQ4_spec (Pos.size_nat p) p i0 i1 r 0 0 (le_n _) (Z.le_refl 0) eq_refl eq_refl ltac:(lia) H) as R.
rewrite Z.pow_0_r in R. lia.
Qed.
End P2Q.
Definition z2l (z : Z) : option PrimInt63.int :=
match z with
| Z0 => Some i0
| Zpos p => match P2Q.p2iQ4 p i0 i1 with Some r => if PrimInt63.ltb r B59 then Some r else None | None => None end
| Zneg _ => None
end.
Definition z2b (z : Z) : option PrimInt63.int :=
match z with
| Z0 => Some B59
| Zpos p => match P2Q.p2iQ4 p i0 i1 with Some r => if PrimInt63.ltb r B59 then Some (PrimInt63.add B59 r) else None | None => None end
| Zneg p => match P2Q.p2iQ4 p i0 i1 with Some r => if PrimInt63.leb r B59 then Some (PrimInt63.sub B59 r) else None | None => None end
end.
Definition iv_of (k m : Z) : option (PrimInt63.int * PrimInt63.int) :=
match z2b k with Some a => match z2l m with Some l => Some (a, PrimInt63.add a l) | None => None end | None => None end.
Definition ent_iv (K : kentry) : option (PrimInt63.int * PrimInt63.int) :=
match K with
| KWord (SA _ kk) w' _ => iv_of kk (Z.of_nat w')
| KZero (SA _ kk) (ELit l0) | KFill (SA _ kk) (ELit l0) _ | KUnk (SA _ kk) (ELit l0) =>
match l0 with Zpos _ => iv_of kk l0 | _ => None end
| KBlob (SA _ kk) (ELit l0) _ => iv_of kk l0
| KImg lo hi => if Z.ltb lo hi then match z2b lo, z2b hi with Some a, Some b => Some (a, b) | _, _ => None end else None
| _ => None
end.
Lemma wB_val : ltac2:(TCodec.tc2 tcn__FxCarry "8'G'N&Q9&[M+2+QO%3221%73651"). Proof. reflexivity. Qed.
Lemma add_nov : ltac2:(TCodec.tc2 tcn__FxCarry "J&Q2&[G&[C&Q8r2%211r1%411%6231&[M+2+QO%3221%<251'G'N&Q1r3%221>%@11%A13%C21@%83731p0:1pQP4H1pQP0I1").
Proof.
intros x y H. rewrite Uint63Axioms.add_spec, wB_val.
pose proof (Uint63.to_Z_bounded x). pose proof (Uint63.to_Z_bounded y). rewrite wB_val in *.
apply Z.mod_small. lia.
Qed.
Lemma sub_nov : ltac2:(TCodec.tc2 tcn__FxCarry "E&Q2&[E&Q8r1%211r2%411%6231'G'N&Q7r3%2217%;11&[N%=14%221:%93841p0;1pQP4C1pQP0D1").
Proof.
intros x y H. rewrite Uint63Axioms.sub_spec, wB_val.
pose proof (Uint63.to_Z_bounded x). pose proof (Uint63.to_Z_bounded y). rewrite wB_val in *.
apply Z.mod_small. lia.
Qed.
Lemma i0_val : ltac2:(TCodec.tc2 tcn__FxCarry "7'G'N&Q8&W2%211z%63521"). Proof. reflexivity. Qed.
Lemma i1_val : ltac2:(TCodec.tc2 tcn__FxCarry "7'G'N&Q8&W3%211+1%63521"). Proof. reflexivity. Qed.
Lemma m61_val : ltac2:(TCodec.tc2 tcn__FxCarry ":'G'N&Q8&X4%211&[M+2+QM%3221%93851"). Proof. reflexivity. Qed.
Lemma B59_val : ltac2:(TCodec.tc2 tcn__FxCarry ":'G'N&Q8&TJ%211&[M+2+QK%3221%93851"). Proof. reflexivity. Qed.
Lemma ileb_le : ltac2:(TCodec.tc2 tcn__FxCarry "B&Q2'G'8&Q3r2r1%3221(E%73621&[E&Q8r3%211%319%5221p071pQP4@1pQP0A1").
Proof. intros x y H. apply Uint63Axioms.leb_spec. exact H. Qed.
Lemma iltb_lt : ltac2:(TCodec.tc2 tcn__FxCarry "B&Q2'G'8&Q5r2r1%3221(E%73621&[G&Q8r3%211%319%5221p071pQP4@1pQP0A1").
Proof. intros x y H. apply Uint63Axioms.ltb_spec. exact H. Qed.
Lemma p2iS_spec : ltac2:(TCodec.tc2 tcn__FxCarry "Q9'Q0&Q2'F&[Ez&Q8r3%211%5241&[Gr2%611%3251%;251'G'?%11?&Y?r5r4%3321>(6%12E<%93731'N&[C%E18&[J%G19(Or6%211%5241%8271%D3:K1p0<1p0G1pn<Q41pn:Q51ph8Q61pn2Q81").
Proof.
induction p as [q IH|q IH|]; intros acc pw r Ha H; cbn [p2iS] in H;
(destruct (PrimInt63.ltb m61 pw) eqn:El; [discriminate|]);
(assert (Q : Uint63Axioms.to_Z pw <= 2 ^ 61) by (rewrite <- m61_val; destruct (Z.le_gt_cases (Uint63Axioms.to_Z pw) (Uint63Axioms.to_Z m61)) as [X|X]; [exact X|];
apply Uint63Axioms.ltb_spec in X; congruence));
(assert (E2 : Uint63Axioms.to_Z (PrimInt63.add pw pw) = Uint63Axioms.to_Z pw + Uint63Axioms.to_Z pw) by (apply add_nov; lia)).
- assert (E1 : Uint63Axioms.to_Z (PrimInt63.add acc pw) = Uint63Axioms.to_Z acc + Uint63Axioms.to_Z pw) by (apply add_nov; lia).
apply IH in H; [|rewrite E1, E2; lia]. rewrite H, E1, E2, Pos2Z.inj_xI. ring.
- apply IH in H; [|rewrite E2; lia]. rewrite H, E2, Pos2Z.inj_xO. ring.
- injection H as <-. rewrite add_nov by lia. lia.
Qed.
Lemma p2iS_val : ltac2:(TCodec.tc2 tcn__FxCarry "H'Q0&Q2'G'?%113&Y?r2&W2&W3%43321(6r1%22;1%;3941'N&Q8%11:(Or3%211%B3641p081pn<E1pn2G1").
Proof. intros p r H. rewrite (p2iS_spec p i0 i1 r); [rewrite i0_val, i1_val; lia|rewrite i0_val, i1_val; lia|exact H]. Qed.
Lemma z2l_val : ltac2:(TCodec.tc2 tcn__FxCarry "O'N&Q2'G'?%113&[:r2%211(6r1%2291%93741'F&Q8%118r3%>3@21&[Ez%2214&[G&[M+2+QK%3221%52:1%>271%?2;1p0A1pl>L1pQP6N1").
Proof.
intros z l H. destruct z as [|p|p]; cbn [z2l] in H; [injection H as <-; rewrite i0_val; lia| |discriminate].
destruct (P2Q.p2iQ4 p i0 i1) as [r|] eqn:E; [|discriminate]. destruct (PrimInt63.ltb r B59) eqn:EB; [|discriminate].
injection H as <-. apply P2Q.p2iQ4_val in E. destruct E as [E _]. apply iltb_lt in EB. rewrite B59_val in EB. lia.
Qed.
Lemma z2b_val : ltac2:(TCodec.tc2 tcn__FxCarry "Q2'N&Q2'G'?%113&[8r2%211(6r1%2291%93741'F&Q8%118&[Cr3&[M+2+QK%3221%6251%D3F81&[E&[L%115%321:&[G%12<8%A231%B281p0D1ph6O1pQP6Q11").
Proof.
intros z a H. destruct z as [|p|p]; cbn [z2b] in H.
- injection H as <-. rewrite B59_val. lia.
- destruct (P2Q.p2iQ4 p i0 i1) as [r|] eqn:E; [|discriminate]. destruct (PrimInt63.ltb r B59) eqn:EB; [|discriminate].
injection H as <-. apply P2Q.p2iQ4_val in E. destruct E as [E _]. apply iltb_lt in EB. rewrite B59_val in EB.
rewrite add_nov by (rewrite B59_val; lia). rewrite B59_val. lia.
- destruct (P2Q.p2iQ4 p i0 i1) as [r|] eqn:E; [|discriminate]. destruct (PrimInt63.leb r B59) eqn:EB; [|discriminate].
injection H as <-. apply P2Q.p2iQ4_val in E. destruct E as [E _]. apply ileb_le in EB. rewrite B59_val in EB.
rewrite sub_nov by (rewrite B59_val; lia). rewrite B59_val. lia.
Qed.
Lemma iv_of_val : ltac2:(TCodec.tc2 tcn__FxCarry "Q>'N&Q2'G'?'C%1244%311&WAr4r3%3221(6(Br2r1%34>>21%52;1%?3;71'F&Q8%11;&[Cr5&[M+2+QK%3221%6251%J3L81%:1@%928F%:215%N3Q031&[Ez%221K&[G%12M;%D231%E271%F2<1p0H1piHQ91ph6Q:1plNQ<1pkFQ=1").
Proof.
intros k m a e H. unfold iv_of in H. destruct (z2b k) as [a'|] eqn:Ea; [|discriminate]. destruct (z2l m) as [l|] eqn:El; [|discriminate].
injection H as <- <-. apply z2b_val in Ea. apply z2l_val in El. destruct Ea as [Ea1 Ea2]. destruct El as [El1 El2].
split; [exact Ea1|]. split; [|exact El2]. rewrite add_nov by lia. lia.
Qed.
Lemma iv_of_kb : ltac2:(TCodec.tc2 tcn__FxCarry "Q4'N&Q2'G'?'C%1244%311&WAr4r3%3221(6(Br2r1%34>>21%52;1%?3;71'F&[E&[L&[M+2+QK%3221%511r5%8221&[G%1235%<231p0>1piHO1ph6Q01plNQ21pkFQ31").
Proof.
intros k m a e H. unfold iv_of in H. destruct (z2b k) as [a'|] eqn:Ea; [|discriminate]. apply z2b_val in Ea. apply Ea.
Qed.
Definition two62 : Z := 2 ^ 62.
Definition z2i (z : Z) : option PrimInt63.int :=
match z with Z0 => Some i0 | Zpos p => P2Q.p2iQ4 p i0 i1 | Zneg _ => None end.
Definition ab2i (o : option (Z * Z)) : option (PrimInt63.int * PrimInt63.int) :=
match o with Some (A, B) => match z2i A, z2i B with Some a, Some b => Some (a, b) | _, _ => None end | None => None end.
Definition rng2l (o : option (Z * Z)) : option (PrimInt63.int * PrimInt63.int) :=
match o with
| Some (lo, hi) => match z2l lo with Some a => match z2l hi with Some b => Some (a, b) | None => None end | None => None end
| None => None
end.
Definition mk_abj (rng : option (Z * Z)) (iv : option (PrimInt63.int * PrimInt63.int)) : option (PrimInt63.int * PrimInt63.int) :=
match iv with
| Some (c, d) => match rng2l rng with Some (lo1, hi1) => Some (PrimInt63.add hi1 d, PrimInt63.add lo1 c) | None => None end
| None => None
end.
Record sxi := SXI { si_sx : stx; si_ab : option (Z * Z); si_bx : option bx; si_ke : Z;
si_iv : option (PrimInt63.int * PrimInt63.int);
si_abj : option (PrimInt63.int * PrimInt63.int); si_eabj : option (PrimInt63.int * PrimInt63.int); si_a2j : option (PrimInt63.int * PrimInt63.int) }.
Definition xget (X : ptree (option bx)) (bid : positive) : option bx :=
match pt_get X bid with Some o => o | None => None end.
Definition mk_sxi (X : ptree (option bx)) (sx : stx) : sxi :=
let ab := match sp_rng (sx_sp sx) with
| Some (lo1, hi1) => Some (hi1 + a_off (sx_a sx) + sx_m1 sx, lo1 + a_off (sx_a sx))
| None => None
end in
let iv := iv_of (a_off (sx_a sx)) (Z.of_nat (sx_w sx)) in
let abj := mk_abj (sp_rng (sx_sp sx)) iv in
SXI sx ab (xget X (sx_bid sx)) (a_off (sx_a sx) + Z.of_nat (sx_w sx)) iv abj
(if obr_eqb (sx_br sx) (sp_rng (sx_sp sx)) then match abj with Some (A, B) => Some (B, A) | None => None end else None)
(match sp_h1 (sx_sp sx) with
| Some h1 => if Z.eqb h1 (Z.of_nat (sx_w sx)) then abj else None
| None => None
end).
Definition gq_of (g : gval) : option (Z * Z) :=
match g with (b, obr, (glo, ghi)) => match obr with Some (lo2, hi2) => Some (glo + lo2, ghi + hi2) | None => None end end.
Definition verdictF (si : sxi) (b : positive) (gq : option (Z * Z)) : bool :=
if Pos.eqb b (sx_bid (si_sx si)) then false else
match si_ab si, gq with
| Some (A, B), Some (GL, GH) => if Z.leb A GL then true else Z.leb GH B
| _, _ => false
end.
Record gxi := GXI { gx_b : expr; gx_bx : option bx }.
Definition linV (bc : bctx) (si : sxi) (b : positive) (obr : option (Z * Z)) (glo ghi : Z) (gx : option gxi) : bool :=
match gx with
| Some x =>
if Pos.eqb b (sx_bid (si_sx si)) then false else
if (if Z.leb 0 (ghi - glo) then Z.ltb (ghi - glo) two63z else false) then
let sx := si_sx si in
ranges_apart_pcF bc (si_bx si) (gx_bx x) (sx_sp sx) (a_base (sx_a sx)) (a_off (sx_a sx)) (elen (sx_w sx)) obr (gx_b x) glo (ELit (ghi - glo))
else false
| None => false
end.
Fixpoint mk_flF (bc : bctx) (b : positive) (gq : option (Z * Z)) (obr : option (Z * Z)) (glo ghi : Z) (gx : option gxi) (sis : list sxi) : list (sxi * list sxi) :=
match sis with
| si :: srest => if verdictF si b gq then mk_flF bc b gq obr glo ghi gx srest
else if linV bc si b obr glo ghi gx then mk_flF bc b gq obr glo ghi gx srest
else (si, srest) :: mk_flF bc b gq obr glo ghi gx srest
| [] => []
end.
Definition is_litb (e : expr) : bool := match e with ELit _ => true | _ => false end.
Definition gflF : Type := (gval * option gxi * list (sxi * list sxi))%type.
Definition mk_glF (bc : bctx) (info : ptree binfo) (X : ptree (option bx)) (bnds : gtab) (sis : list sxi) : ptree gflF :=
pt_map (fun g : gval =>
match g with
| (b, obr, (glo, ghi)) =>
let gx := match pt_get info b with
| Some bi => if is_litb (bi_base bi) then None else Some (GXI (bi_base bi) (xget X b))
| None => None
end in
(g, gx, mk_flF bc b (gq_of g) obr glo ghi gx sis)
end) bnds.
Definition member_ok (K : kentry) (g : gval) (gx : option gxi) : bool :=
match gx with
| None => true
| Some x =>
match g, kdescr K with
| (_, _, (glo, ghi)), Some (kb, kk, Some m) =>
if expr_eqb kb (gx_b x) then (if Z.leb glo kk then Z.leb (kk + m) ghi else false) else false
| _, _ => false
end
end.
Definition g1cF (bc : bctx) (si : sxi) (K : kentry) : list kentry :=
match K with
| KImg lo hi =>
match a_base (sx_a (si_sx si)), si_ab si with
| ELit 0, _ => g1cBF bc (si_sx si) K
| _, Some (A, B) =>
if (if (let d := hi - lo in if Z.leb 0 d then Z.ltb d two64 else false) then (if Z.leb A lo then true else Z.leb hi B) else false)
then [K] else g1cBF bc (si_sx si) K
| _, None => g1cBF bc (si_sx si) K
end
| _ => g1cBF bc (si_sx si) K
end.
Fixpoint chain_slowF (bc : bctx) (sis : list sxi) (l : list kentry) : list kentry :=
match sis with
| [] => l
| si :: rest => chain_slowF bc rest (flat_map (g1cF bc si) l)
end.
Fixpoint chainK2F (bc : bctx) (xo : option bx) (sis : list sxi) (K : kentry) (okb : option expr) (same_of : positive -> bool)
(br2 : option (Z * Z)) : list kentry :=
match sis with
| [] => [K]
| si :: rest =>
let sx := si_sx si in
match prune1pcKF bc (si_bx si) xo (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) K (same_of (sx_bid sx)) br2 with
| PKeep => chainK2F bc xo rest K okb same_of br2
| PRepl l =>
match okb with
| Some kb =>
flat_map (fun K' => match kbase K' with
| Some kb' => if expr_eqb kb' kb then chainK2F bc xo rest K' okb same_of br2 else chain_slowF bc rest [K']
| None => chain_slowF bc rest [K']
end) l
| None => chain_slowF bc rest l
end
end
end.
Fixpoint chainKFF (bc : bctx) (xo : option bx) (fl : list (sxi * list sxi)) (K : kentry) (okb : option expr) (same_of : positive -> bool)
(br2 : option (Z * Z)) : list kentry :=
match fl with
| [] => [K]
| (si, rest) :: fl' =>
let sx := si_sx si in
match prune1pcKF bc (si_bx si) xo (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) K (same_of (sx_bid sx)) br2 with
| PKeep => chainKFF bc xo fl' K okb same_of br2
| PRepl l =>
match okb with
| Some kb =>
flat_map (fun K' => match kbase K' with
| Some kb' => if expr_eqb kb' kb then chainK2F bc xo rest K' okb same_of br2 else chain_slowF bc rest [K']
| None => chain_slowF bc rest [K']
end) l
| None => chain_slowF bc rest l
end
end
end.
Definition is_fact_entry (K : kentry) : bool :=
match K with KAlign _ _ | KRange _ _ _ | KWr _ _ | KDisj _ _ _ _ => true | _ => false end.
Fixpoint entriesGF (bc : bctx) (X : ptree (option bx)) (sis : list sxi) (gl : ptree gflF) (kn : list kentry) (infos : list (option einfo)) : list kentry :=
match kn, infos with
| K :: rest, oi :: irest =>
(match oi with
| Some ei =>
let okb := kbase K in
let same_of := match okb with Some _ => Pos.eqb (ei_bid ei) | None => fun _ => false end in
let br2 := match okb with Some _ => ei_br ei | None => None end in
match pt_get gl (ei_gid ei) with
| Some (g, gx, fl) =>
if inb g ei then
(if member_ok K g gx then chainKFF bc (xget X (ei_bid ei)) fl K okb same_of br2
else match g with
| (b, obr, (glo, ghi)) => chainKFF bc (xget X (ei_bid ei)) (mk_flF bc b (gq_of g) obr glo ghi None sis) K okb same_of br2
end)
else chainK2F bc (xget X (ei_bid ei)) sis K okb same_of br2
| None => chainK2F bc (xget X (ei_bid ei)) sis K okb same_of br2
end
| None => if is_fact_entry K then [K] else chainK2F bc None sis K None (fun _ => false) None
end) ++ entriesGF bc X sis gl rest irest
| _, _ => []
end.
Fixpoint store_bases (sxs : list stx) (seen : ptree unit) : list expr :=
match sxs with
| [] => []
| sx :: rest => match pt_get seen (sx_bid sx) with
| Some _ => store_bases rest seen
| None => a_base (sx_a sx) :: store_bases rest (pt_set (sx_bid sx) tt seen)
end
end.
Fixpoint stores_partF (bc : bctx) (sis : list sxi) : list kentry :=
match sis with
| [] => []
| si :: newer => let sx := si_sx si in
stores_partF bc newer ++ chainK2F bc (si_bx si) newer (KWord (sx_a sx) (sx_w sx) (sx_v sx)) (Some (a_base (sx_a sx))) (Pos.eqb (sx_bid sx)) (sx_br sx)
end.
Definition num_sub (bc : bctx) (b : expr) (k n : Z) (c : saddr) (m : expr) : bool :=
if (if expr_eqb b (a_base c) then Z.leb (a_off c) k else false) then
match xloB bc m with Some ml => Z.leb (k + n) (a_off c + ml) | None => false end
else false.
Fixpoint disj_both (bc : bctx) (kn : list kentry) (b1 : expr) (k1 n1 : Z) : list (saddr * expr) * list (saddr * expr) :=
match kn with
| [] => ([], [])
| KDisj c1 m1 c2 m2 :: rest =>
let '(r, rx) := disj_both bc rest b1 k1 n1 in
let x2 := xinsideB bc b1 k1 (ELit n1) (a_base c2) (a_off c2) m2 in
let x1 := xinsideB bc b1 k1 (ELit n1) (a_base c1) (a_off c1) m1 in
let r1 := if (if num_sub bc b1 k1 n1 c2 m2 then true else x2) then (c1, m1) :: r else r in
let rx1 := if x2 then (c1, m1) :: rx else rx in
((if (if num_sub bc b1 k1 n1 c1 m1 then true else x1) then (c2, m2) :: r1 else r1),
(if x1 then (c2, m2) :: rx1 else rx1))
| _ :: rest => disj_both bc rest b1 k1 n1
end.
Definition mk_sprepF (bc : bctx) (kd : list kentry) (b1 : expr) (k1 : Z) (n1 : expr) : sprep :=
match n1 with
| ELit z1 =>
if Z.eqb (zlit64 z1) z1 then
let '(D, Dx) := disj_both bc kd b1 k1 z1 in SPrep (base_rangeB bc b1) (xhiB bc n1) D Dx
else SPrep (base_rangeB bc b1) (xhiB bc n1) (disj_sidesB bc kd b1 k1 (zlit64 z1)) (disj_sides_xB bc kd b1 k1 n1)
| _ => SPrep (base_rangeB bc b1) (xhiB bc n1) [] (disj_sides_xB bc kd b1 k1 n1)
end.
Fixpoint mk_stxsF (bc : bctx) (kd : list kentry) (log : list sentry) (t : ntab) : list stx * ntab :=
match log with
| [] => ([], t)
| SE a w v :: older =>
let '(sxs, t1) := mk_stxsF bc kd older t in
let '(r, t2) := intern bc t1 (a_base a) in
let '(bid, bi) := r in
(sxs ++ [STX a w v (mk_sprepF bc kd (a_base a) (a_off a) (elen w)) bid (bi_br bi)], t2)
end.
Definition carryGF (bc : bctx) (log : list sentry) (kn : list kentry) : list kentry :=
let '(sxs, t0) := mk_stxsF bc (be_kd (mk_bext bc)) log nt_empty in
let '(r, gs) := scan_entries bc kn t0 gst_empty in
let '(infos, t1) := r in
let sbs := store_bases sxs PTLeaf in
let X := pt_map (fun bi => if existsbF (fun sb => shares_var sb (bi_base bi)) sbs then Some (mk_bx bc (bi_base bi)) else None) (nt_info t1) in
let sis := map (mk_sxi X) sxs in
stores_partF bc sis ++ entriesGF bc X sis (mk_glF bc (nt_info t1) X (gs_bnds gs) sis) kn infos.
Definition carryKF1 (bc : bctx) (log : list sentry) (kn : list kentry) (hints : list bool)
: list kentry * list sidecond * list bool :=
match log, hints with
| [], _ => (kn, [], hints)
| _, [] => (carryGF bc log kn, [], [])
| _, _ => carryB bc log kn hints
end.
Ltac fe := repeat (apply functional_extensionality; intros ?).
Lemma zmod64_fe : ltac2:(TCodec.tc2 tcn__FxCarry "='G'NpQP611&RC&[Ir1&[M+2+R0%3221%6251qQP6:1%<3:91").
Proof. fe. apply zmod64_eq. Qed.
Lemma lin_range_shift : forall rng c ts,
lin_range rng c ts = match lin_range rng 0 ts with Some (lo, hi) => Some (lo + c, hi + c) | None => None end.
Proof.
intros rng c ts. induction ts as [|[k a] rest IH]; cbn [lin_range].
- reflexivity.
- rewrite IH. destruct (rng a) as [[al ah]|]; [|reflexivity].
destruct (lin_range rng 0 rest) as [[lo hi]|]; [|reflexivity].
destruct (Z.leb 0 k); f_equal; f_equal; lia.
Qed.
Lemma lin_testB_mono : ltac2:(TCodec.tc2 tcn__FxCarry "Q<'RM'N'<'C'QJ%2241%411'8p071p081'Gr4r2r1%3221(E%63921&[Cr3r7%3221%4292%;221%=3@18p081pQP4H1pQP0I1&SJr6%24:1B;%D3G1?r8%?2=4r5%74321@%I3L1Dp061p0;1ph2M1ph0N1poDQ21piDQ81pi4Q91phFQ;1").
Proof.
intros bc c d ts T1 T2 HT. unfold lin_testB, lin_test_relB.
rewrite (lin_range_shift _ c ts), (lin_range_shift _ (c + d) ts).
destruct (lin_range (erangeB bc) 0 ts) as [[lo hi]|] eqn:E0.
- destruct (T1 (lo + c) (hi + c)) eqn:E1.
+ intros _. replace (lo + (c + d)) with (lo + c + d) by lia. replace (hi + (c + d)) with (hi + c + d) by lia.
rewrite (HT _ _ E1). reflexivity.
+ intros H. destruct (T2 (lo + (c + d)) (hi + (c + d))); [reflexivity|].
destruct (bc_fs bc) as [|f fs]; [discriminate|].
destruct (sum_subst (f :: fs) ts 0 0 false) as [[ts' [lo0 hi0]] [|]]; [|discriminate].
rewrite (lin_range_shift _ c ts') in H. rewrite (lin_range_shift _ (c + d) ts').
destruct (lin_range (erangeB bc) 0 ts') as [[a b]|]; [|discriminate].
replace (a + (c + d) + lo0) with (a + c + lo0 + d) by lia. replace (b + (c + d) + hi0) with (b + c + hi0 + d) by lia.
apply HT. exact H.
- intros H.
destruct (bc_fs bc) as [|f fs]; [discriminate|].
destruct (sum_subst (f :: fs) ts 0 0 false) as [[ts' [lo0 hi0]] [|]]; [|discriminate].
rewrite (lin_range_shift _ c ts') in H. rewrite (lin_range_shift _ (c + d) ts').
destruct (lin_range (erangeB bc) 0 ts') as [[a b]|]; [|discriminate].
replace (a + (c + d) + lo0) with (a + c + lo0 + d) by lia. replace (b + (c + d) + hi0) with (b + c + hi0 + d) by lia.
apply HT. exact H.
Qed.
Lemma T0_mono : ltac2:(TCodec.tc2 tcn__FxCarry "K'N&[Ezr1%3221'G'8&[Fr2%2271q0:1qlH;1%1249(E%93821&[Cr3r5%3221%42;2%9221%@3?18p081pQP4G1pQP0H1p0E1piDJ1").
Proof. intros d Hd x y H. cbv beta in *. apply Z.leb_le in H. apply Z.leb_le. lia. Qed.
Lemma lin_ge0_scaledB_mono : ltac2:(TCodec.tc2 tcn__FxCarry "O'RM'N'<'C'QJ%2241%411&[Ezr2%3221'G'8&SHr5r4%33217(E%73621r6&[C%1276r3%:3421%=3<17p071p0@1poDE1piDK1p:L1phFN1").
Proof.
intros bc C d ts Hd H. unfold lin_ge0_scaledB in *.
destruct (if Z.ltb 0 (srl_scale_need ts) then Z.leb (srl_scale_need ts) 24 else false) eqn:Ej; [|discriminate].
assert (Hj : 0 < srl_scale_need ts) by (destruct (Z.ltb_spec 0 (srl_scale_need ts)); [lia|discriminate]).
destruct (srl_expandB bc (List.map (fun t => (2 ^ srl_scale_need ts * fst t, snd t)) ts)) as [c2 t2].
destruct (if has_srl t2 then srl_expandB bc t2 else (0, t2)) as [c3 t3].
replace (2 ^ srl_scale_need ts * (C + d) + c2 + c3) with ((2 ^ srl_scale_need ts * C + c2 + c3) + 2 ^ srl_scale_need ts * d) by ring.
assert (Hsd : 0 <= 2 ^ srl_scale_need ts * d) by (apply Z.mul_nonneg_nonneg; [apply Z.pow_nonneg; lia|exact Hd]).
apply (lin_testB_mono _ _ _ _ _ _ (T0_mono _ Hsd)). exact H.
Qed.
Lemma lin_ge0B_mono : ltac2:(TCodec.tc2 tcn__FxCarry "QI'RM&RA'G'8&TIr5r2%3221r4%5241%83731r6%8216%9225%<3;21'<'C'N'QJ%3221%511&R@%11>%21<%F3421&[E&[N&R?r8%211r7%411%6231%61F%71M%9221%;241&SGr:r9%3321<(E%Q83Q721r;%731@>%Q;3Q:14p041p0;1p0H1p0I1p0Q41p0Q91pmDQC1pn6QD1pmBQE1pn4QF1phFQH1").
Proof.
intros bc pos neg pos' neg' Hnp Hnn Hlp Hln Hc H. unfold lin_ge0B in *. rewrite Hnp, Hnn, Hlp, Hln.
set (ts := lsub_e (xt_lin pos) (xt_lin neg)) in *.
set (C := xt_const pos - xt_const neg) in *.
replace (xt_const pos' - xt_const neg') with (C + (xt_const pos' - xt_const neg' - C)) by lia.
set (d := xt_const pos' - xt_const neg' - C).
assert (Hd : 0 <= d) by (unfold d; lia).
pose proof (T0_mono d Hd) as HT.
destruct (xt_nowrapB bc pos), (xt_nowrapB bc neg); cbn [andb] in *; try discriminate.
destruct (lin_testB bc C ts (fun lo _ => Z.leb 0 lo)) eqn:E1.
{ rewrite (lin_testB_mono bc C d ts _ _ HT E1). reflexivity. }
destruct (lin_testB bc (C + d) ts (fun lo _ => Z.leb 0 lo)); [reflexivity|].
destruct (srl_expandB bc ts) as [c2 t2].
destruct (lin_testB bc (C + c2) t2 (fun lo _ => Z.leb 0 lo)) eqn:E2.
{ replace (C + d + c2) with (C + c2 + d) by lia. rewrite (lin_testB_mono bc _ d t2 _ _ HT E2). reflexivity. }
destruct (lin_testB bc (C + d + c2) t2 (fun lo _ => Z.leb 0 lo)); [reflexivity|].
destruct (has_srl t2).
- destruct (srl_expandB bc t2) as [c3 t3].
destruct (lin_testB bc (C + c2 + c3) t3 (fun lo _ => Z.leb 0 lo)) eqn:E3.
{ replace (C + d + c2 + c3) with (C + c2 + c3 + d) by lia. rewrite (lin_testB_mono bc _ d t3 _ _ HT E3). reflexivity. }
destruct (lin_testB bc (C + d + c2 + c3) t3 (fun lo _ => Z.leb 0 lo)); [reflexivity|].
apply lin_ge0_scaledB_mono; assumption.
- apply lin_ge0_scaledB_mono; assumption.
Qed.
Lemma snorm_small : ltac2:(TCodec.tc2 tcn__FxCarry "A'N'F&[E&R2r1%3221&[G&R=%2241%8241'G&R8r2%211%43>12p061pkF@1").
Proof.
intros k [H1 H2]. unfold snorm. destruct (Z.leb_spec mtwo63z k); [|lia]. destruct (Z.ltb_spec k two63z); [|lia]. reflexivity.
Qed.
Lemma two63z_val : ltac2:(TCodec.tc2 tcn__FxCarry "5'G'N&R=+XPPPPPPPPPPP0%43321"). Proof. reflexivity. Qed.
Lemma mtwo63z_val : ltac2:(TCodec.tc2 tcn__FxCarry "5'G'N&R2-XPPPPPPPPPPP0%43321"). Proof. reflexivity. Qed.
Lemma two64_val : ltac2:(TCodec.tc2 tcn__FxCarry "5'G'N&R>+`PPPPPPPPPPP0%43321"). Proof. reflexivity. Qed.
Lemma lin_nowrapRB_lit : ltac2:(TCodec.tc2 tcn__FxCarry "H'RM'N'F&[Ezr1%3221&[G&R=%2241%8241'G'8&SIr3(QBr2%211%5241(E%93821p0;1pQP6E1phFG1").
Proof.
intros bc z Hz. unfold lin_nowrapRB. cbn [lin_of fst snd srl_expandB].
rewrite snorm_small by (rewrite ?mtwo63z_val, ?two63z_val in *; lia).
unfold lin_testB. cbn [lin_range]. rewrite ?two63z_val in Hz.
destruct (Z.leb_spec 0 (z + 0)); [|lia]. destruct (Z.ltb_spec (z + 0) two64); [reflexivity|]. rewrite two64_val in *. lia.
Qed.
Lemma xinside0B_mono : ltac2:(TCodec.tc2 tcn__FxCarry "QE'RM'QJ'N&[Ezr1%3221&[Gr7&R=%3221r8%9281r:r5%<221&[Cr6%2214r;%4217%B231'G'8&TFr>r=r<(QB%11:r9%776542B1D(E%;3:21r?%71K%<72;I1AG6%?3>15p051p0B1p0I1p0M1p0Q01p0Q51pm:Q:1pkHQ;1plNQ=1piBQ=1pi@Q?1pm8Q?1pkFQ@1ph>QB1phFQD1").
Proof.
intros bc b k n cb co m k' n' Hn' Hn Hn0 Hk Hkn H. unfold xinside0B in *.
destruct (lin_ge0B bc [(b, k)] [(cb, co)]) eqn:E1; [|discriminate].
rewrite (lin_ge0B_mono bc [(b, k)] [(cb, co)] [(b, k')] [(cb, co)]); try reflexivity; [|cbn [xt_const]; lia|exact E1].
revert H. apply lin_ge0B_mono; try reflexivity.
- cbn [xt_nowrapB]. rewrite !lin_nowrapRB_lit by (rewrite ?two63z_val in *; lia). reflexivity.
- cbn [xt_const lin_of fst]. rewrite !snorm_small by (rewrite ?mtwo63z_val, ?two63z_val in *; lia). lia.
Qed.
Lemma xinside_numB_mono : ltac2:(TCodec.tc2 tcn__FxCarry "QH'RM'QJ'N&[Ezr1%3221&[Gr7&R>%3221r8%9281r:r5%<221&[Cr6%2214r;%4217%B231%?25='G'8&THr?r>r=(QBr<%211r9%877652>D1(E%<3;21r@%81J%=72<618CI%@3?15p051p0C1p0E1p0L1p0Q01p0Q31p0Q81pm:Q=1pkHQ>1plNQ@1piBQ@1pi@QB1pm8QB1pkFQC1ph>QE1phFQG1").
Proof.
intros bc b k n cb co m k' n' Hn' Hn Hn0 Hk Hkn Hn2 H. unfold xinside_numB in *.
destruct (xloB bc cb) as [lo2|]; [|discriminate]. destruct (xhiB bc cb) as [hi2|]; [|discriminate].
destruct (Z.eqb lo2 hi2); [|discriminate].
destruct (base_rangeB bc b) as [[lo1 hi1]|]; [|discriminate].
cbn [xhiB] in *. unfold zlit64 in *.
destruct (Z.leb_spec 0 n), (Z.ltb_spec n two64); try lia. destruct (Z.leb_spec 0 n'), (Z.ltb_spec n' two64); try lia.
cbn [andb] in *. destruct (xloB bc m) as [l2|]; [|discriminate].
apply andb_prop in H as [A1 A2]. apply Z.leb_le in A1. apply Z.leb_le in A2.
apply andb_true_intro. split; apply Z.leb_le; lia.
Qed.
Lemma xinsideB_mono : ltac2:(TCodec.tc2 tcn__FxCarry "QE'RM'QJ'N&[Ezr1%3221&[Gr7&R=%3221r8%9281r:r5%<221&[Cr6%2214r;%4217%B231'G'8&TGr>r=r<(QB%11:r9%776542B1D(E%;3:21r?%71K%<72;I1AG6%?3>15p051p0B1p0I1p0M1p0Q01p0Q51pm:Q:1pkHQ;1plNQ=1piBQ=1pi@Q?1pm8Q?1pkFQ@1ph>QB1phFQD1").
Proof.
intros bc b k n cb co m k' n' Hn' Hn Hn0 Hk Hkn H. unfold xinsideB in *. rewrite two63z_val in Hn.
destruct (shares_var b cb).
- apply (xinside0B_mono bc b k n); try assumption; rewrite ?two63z_val; lia.
- destruct (novars cb); [|discriminate]. apply (xinside_numB_mono bc b k n); try assumption; rewrite ?two64_val; lia.
Qed.
Lemma sub_itvB_mono : ltac2:(TCodec.tc2 tcn__FxCarry "QA'RM'QJ'N'R5&[Ezr1%3221&[Gr6&R=%3221r7%9281r9r5%<221&[C%1293r:%3216%A231'G'8&T<r=r<r;r8%56432:?1(E%93821r>%96185E>C%<3;14p041p0?1p0E1p0I1p0L1p0Q11pm:Q71pkHQ81plNQ:1pi4Q91pm8Q;1pkFQ<1ph>Q>1phFQ@1").
Proof.
intros bc b k n c m k' n' Hn' Hn Hn0 Hk Hkn H. unfold sub_itvB in *.
assert (NUM : (if (expr_eqb b (a_base c) && Z.leb (a_off c) k)%bool then
match xloB bc m with Some ml => Z.leb (k + n) (a_off c + ml) | None => false end else false) = true ->
(if (expr_eqb b (a_base c) && Z.leb (a_off c) k')%bool then
match xloB bc m with Some ml => Z.leb (k' + n') (a_off c + ml) | None => false end else false) = true).
{ destruct (expr_eqb b (a_base c)); cbn [andb]; [|discriminate].
destruct (Z.leb_spec (a_off c) k); [|discriminate]. destruct (Z.leb_spec (a_off c) k'); [|lia].
destruct (xloB bc m) as [ml|]; [|discriminate]. intros X. apply Z.leb_le in X. apply Z.leb_le. lia. }
assert (RNG : (Z.leb 0 n' && Z.ltb n' two64)%bool = true)
by (apply andb_true_intro; split; [apply Z.leb_le|apply Z.ltb_lt]; rewrite ?two64_val, ?two63z_val in *; lia).
destruct (if (expr_eqb b (a_base c) && Z.leb (a_off c) k)%bool then
match xloB bc m with Some ml => Z.leb (k + n) (a_off c + ml) | None => false end else false) eqn:E1.
- rewrite (NUM eq_refl). reflexivity.
- destruct (if (expr_eqb b (a_base c) && Z.leb (a_off c) k')%bool then
match xloB bc m with Some ml => Z.leb (k' + n') (a_off c + ml) | None => false end else false); [reflexivity|].
rewrite RNG. destruct (Z.leb 0 n && Z.ltb n two64)%bool; [|discriminate].
apply (xinsideB_mono bc b k n); assumption.
Qed.
Lemma in_sidesB_mono : ltac2:(TCodec.tc2 tcn__FxCarry "QD'RM'<'C'R5'QJ%3221%511'N&[Ezr1%3221&[Gr4&R=%3221r5%9281r7%;213&[Cr6%2216r8%4216%A231'G'8&SBr<r;r:r9%554321:(E%93821r=%95187>C%<3;14p041p0?1p0F1p0I1p0L1p0Q11pm:Q61pkHQ71pm8Q81pkFQ91ph>Q=1pRFQ<1phFQC1").
Proof.
intros bc D b k n k' n' Hn' Hn Hn0 Hk Hkn. induction D as [|[c m] r IH]; cbn [in_sidesB]; [discriminate|].
destruct (sub_itvB bc b k n c m) eqn:E.
- rewrite (sub_itvB_mono bc b k n c m k' n' Hn' Hn Hn0 Hk Hkn E). reflexivity.
- intros H. destruct (sub_itvB bc b k' n' c m); [reflexivity|]. apply IH. exact H.
Qed.
Lemma lin_apartB_mono : ltac2:(TCodec.tc2 tcn__FxCarry "Q8'RM'QJ'N&[Er4r2%3221&[Cr3%2214r5%4217%9231'G'8&SFr;r:r9r8r7r6%77654321<(E%;3:21r<%;71:987@F%>3=14p041p0A1p0H1pm@M1pkNN1pm>O1pkLQ01phDQ21pm<Q21pkJQ31phBQ51phFQ71").
Proof.
intros bc b1 k1 n1 b2 k2 n2 k2' n2' Hk Hkn H. unfold lin_apartB, lin_apart0B in *.
destruct (shares_var b1 b2); [|discriminate].
destruct (lin_nowrapRB bc b1), (lin_nowrapRB bc b2); cbn [andb] in *; try discriminate.
replace (fst (lin_of b2) + k2' - fst (lin_of b1) - k1) with ((fst (lin_of b2) + k2 - fst (lin_of b1) - k1) + (k2' - k2)) by lia.
revert H. apply lin_testB_mono. intros x y HT.
apply Bool.orb_true_iff in HT. apply Bool.orb_true_iff. destruct HT as [HT|HT]; apply Z.leb_le in HT; [left|right]; apply Z.leb_le; lia.
Qed.
Lemma zlit64_bounds : ltac2:(TCodec.tc2 tcn__FxCarry "='N'F&[Ez&RBr1%211%5241&[G&R>%2241%:241pQP6<1").
Proof.
intros z. pose proof (Z.mod_pos_bound z two64 ltac:(rewrite two64_val; lia)) as B. unfold zlit64.
destruct (Z.leb_spec 0 z), (Z.ltb_spec z two64); cbn [andb]; lia.
Qed.
Lemma ranges_apart_pcB_mono : ltac2:(TCodec.tc2 tcn__FxCarry "R0'RM'R<'QJ'N'?'C%1233%311'F&[Ezr3%3221&[G&R=%2241%8241r5%9217&[Cr4&RB%11;%4231r6%6218%A231'G'8&T8r>r=r<r;(QBr:%211r9r8r7%61@%<9;:9854321(E%@3?21r?%;1<%<1M%B93A@?2<:G1%E3D16p061p0H1p0Q11p0Q41pQP:QB1pkNQC1pQP<QD1pkLQE1phDQG1phNQC1pQP8QH1pkJQI1phBQK1po6QM1phFQO1").
Proof.
intros bc sp b1 k1 z1 br2 b2 k2 zh k2' z2' Hzh Hk Hkn H. unfold ranges_apart_pcB in *. cbv zeta in *.
assert (Ezh : zlit64 zh = zh).
{ unfold zlit64. rewrite two63z_val in Hzh. destruct (Z.leb_spec 0 zh), (Z.ltb_spec zh two64); cbn [andb]; try reflexivity; rewrite two64_val in *; lia. }
rewrite Ezh in H. pose proof (zlit64_bounds z2') as B2. set (m2' := zlit64 z2') in *.
destruct (match sp_rng sp with Some (lo1, hi1) => match br2 with Some (lo2, hi2) => ((hi1 + k1 + zlit64 z1 <=? lo2 + k2') || (hi2 + k2' + m2' <=? lo1 + k1))%bool | None => false end | None => false end) eqn:EN; [reflexivity|].
destruct (match sp_rng sp with Some (lo1, hi1) => match br2 with Some (lo2, hi2) => ((hi1 + k1 + zlit64 z1 <=? lo2 + k2) || (hi2 + k2 + zh <=? lo1 + k1))%bool | None => false end | None => false end) eqn:EH.
{ exfalso. destruct (sp_rng sp) as [[lo1 hi1]|]; [|discriminate]. destruct br2 as [[lo2 hi2]|]; [|discriminate].
apply Bool.orb_true_iff in EH. apply Bool.orb_false_iff in EN. destruct EN as [N1 N2].
apply Z.leb_gt in N1. apply Z.leb_gt in N2. destruct EH as [X|X]; apply Z.leb_le in X; lia. }
destruct (in_sidesB bc (sp_D sp) b2 k2 zh) eqn:ES.
{ rewrite (in_sidesB_mono bc (sp_D sp) b2 k2 zh k2' m2'); [reflexivity|lia|apply Hzh|apply Hzh|exact Hk|exact Hkn|exact ES]. }
destruct (in_sidesB bc (sp_D sp) b2 k2' m2'); [reflexivity|].
apply (lin_apartB_mono bc b1 k1 (zlit64 z1) b2 k2 zh); assumption.
Qed.
Lemma prune1pcK_keep_lin : ltac2:(TCodec.tc2 tcn__FxCarry "S1'RM'R<'R5'='QJ'QL'N'?'C%1233%311'G%4286%617%6221%811&SEr7%211(6(Br6r5%34CA21r4%62C1%64>=31%82=1%A3=:1&Ir8(QBr1%211%G3N41%611pQP6N1'F&[Ez&[Nr3%221B%5241&[G&R=%2241%:241%:2JB&[Cr9%221E%>21N'8&T8rAr@&QGr?%211&QH%113&QIr>%211r;%J2Q=QA%Q411%>9=<974Q63QC1(E%QK3A21'T4&T7rBr=(:%483EDB=21J(RG%R33721p091p0L1p0Q11p0Q31p0Q?1p0QH1pj4R?1pj:R@1phNR=1plNRB1pl4RC1pl0RF1pRLRF1poNRH1poJRJ1poLRL1po6RN1phFS01").
Proof.
intros bc sp wa w wv K kb kk m br2 glo ghi HD Hkb Hg Hk Hkm H. unfold elen in H.
destruct K as [[b k] w' v|[b k] len|[b k] len bk|lo hi|e' m'|e' lo' hi'|[eb ek] en|c1 m1 c2 m2|[b k] len fc|[b k] len];
cbn [kdescr] in HD; try discriminate.
- injection HD as <- <- <-. unfold prune1pcK, elen. cbv zeta beta iota.
rewrite (ranges_apart_pcB_mono bc sp (a_base wa) (a_off wa) (Z.of_nat w) br2 b glo (ghi - glo) k (Z.of_nat w')); first [reflexivity | assumption | lia].
- destruct len as [z| | | | | | |]; try discriminate. injection HD as <- <- <-. unfold prune1pcK, elen. cbv zeta beta iota.
rewrite (ranges_apart_pcB_mono bc sp (a_base wa) (a_off wa) (Z.of_nat w) br2 b glo (ghi - glo) k z); first [reflexivity | assumption | lia].
- destruct len as [z| | | | | | |]; try discriminate. injection HD as <- <- <-. unfold prune1pcK, elen. cbv zeta beta iota.
rewrite (ranges_apart_pcB_mono bc sp (a_base wa) (a_off wa) (Z.of_nat w) br2 b glo (ghi - glo) k z); first [reflexivity | assumption | lia].
- injection HD as <- _ _. exfalso. apply (Hkb 0). reflexivity.
- destruct len as [z| | | | | | |]; try discriminate. injection HD as <- <- <-. unfold prune1pcK, elen. cbv zeta beta iota.
rewrite (ranges_apart_pcB_mono bc sp (a_base wa) (a_off wa) (Z.of_nat w) br2 b glo (ghi - glo) k z); first [reflexivity | assumption | lia].
- destruct len as [z| | | | | | |]; try discriminate. injection HD as <- <- <-. unfold prune1pcK, elen. cbv zeta beta iota.
rewrite (ranges_apart_pcB_mono bc sp (a_base wa) (a_off wa) (Z.of_nat w) br2 b glo (ghi - glo) k z); first [reflexivity | assumption | lia].
Qed.
Definition BXOK (bc : bctx) (o : option bx) : Prop := forall x, o = Some x -> x = mk_bx bc (bx_b x).
Lemma bx_get_ok : ltac2:(TCodec.tc2 tcn__FxCarry "L'RM'?'UH%211'QJ&TLr3r2%3221'G'C&QN'8%3221&UIr4%231:9(B&QO%11<&SI%126>%54;:31%>3:71p0@1ph>E1pmLG1phFK1").
Proof.
intros bc [x|] b H; [|reflexivity]. cbn [bx_get]. eF.
destruct (expr_eqb (bx_b x) b) eqn:E; [|reflexivity].
apply p_expr_eqb_eq in E. rewrite (H x eq_refl). subst b. reflexivity.
Qed.
Lemma lin_apartF_eq : ltac2:(TCodec.tc2 tcn__FxCarry "O'RM'?'UH%211&TLr3r2%3221r4%5213'G'QJ'N'8pm>21pkL31phD51pm<51pkJ61phB81&X0r5%231>A&SF%113%?3631p0A1p0D1pk8I1pk6J1phFN1").
Proof.
intros bc i1 i2 H1 H2. fe. rename x into b1, x0 into k1, x1 into n1, x2 into b2, x3 into k2, x4 into n2.
unfold lin_apartF, lin_apartB, lin_apart0B. destruct (shares_var b1 b2); [|reflexivity].
rewrite (bx_get_ok _ _ _ H1), (bx_get_ok _ _ _ H2).
destruct (lin_nowrapRB bc b1), (lin_nowrapRB bc b2); reflexivity.
Qed.
Lemma ranges_apart_pcF_eq : ltac2:(TCodec.tc2 tcn__FxCarry "Q5'RM'?'UH%211&TLr3r2%3221r4%5213'G'R<'QJ'N'C%1222%?11'8pm>61pkL61phD81phN51pm<:1pkJ:1phB<1po6>1&YIr5%231DG&T8%113%E3631p0G1p0J1pk8O1pk6Q01phFQ41").
Proof.
intros bc i1 i2 H1 H2. apply functional_extensionality; intros sp. apply functional_extensionality; intros b1.
apply functional_extensionality; intros k1. apply functional_extensionality; intros n1.
apply functional_extensionality; intros br2. apply functional_extensionality; intros b2.
apply functional_extensionality; intros k2. apply functional_extensionality; intros n2.
unfold ranges_apart_pcF, ranges_apart_pcB. rewrite (lin_apartF_eq _ _ _ H1 H2).
destruct n1 as [z1| | | | | | |]; try reflexivity. destruct n2 as [z2| | | | | | |]; try reflexivity. cbv zeta.
destruct (match sp_rng sp with Some (lo1, hi1) => _ | None => false end); [reflexivity|].
destruct (in_sidesB bc (sp_D sp) b2 k2 (zlit64 z2)), (lin_apartB bc b1 k1 (zlit64 z1) b2 k2 (zlit64 z2)); reflexivity.
Qed.
Ltac crush :=
repeat (first [ reflexivity
| match goal with
| |- context [if ?c then _ else _] =>
lazymatch c with context [if _ then _ else _] => fail | _ => destruct c end
| |- context [match ?x with nil => _ | cons _ _ => _ end] =>
lazymatch x with context [if _ then _ else _] => fail | _ => destruct x end
| |- context [match ?x with ELit _ => _ | _ => _ end] => is_var x; destruct x
end ]).
Lemma prune1pcKF_eq : ltac2:(TCodec.tc2 tcn__FxCarry "Q8'RM'?'UH%211&TLr3r2%3221r4%5213'G'R<'R5'='QJ'QL'8'C'N%2211%C11'T4phN21pnB71pRL91poN;1poJ=1poL?1po6A1&YCr5%231GJ&T7%113%H3631p0J1p0M1pk8Q21pk6Q31phFQ71").
Proof.
intros bc i1 i2 H1 H2. fe. rename x into sp, x0 into wa, x1 into w, x2 into wv, x3 into K, x4 into same, x5 into br2.
unfold prune1pcKF, prune1pcK. rewrite (ranges_apart_pcF_eq _ _ _ H1 H2), zmod64_fe. cbv [orb andb]. cbv zeta.
destruct K as [[kb kk] w' v|[kb kk] len|[kb kk] len bk|lo hi|e' m'|e' lo' hi'|[eb ek] en|c1 m1 c2 m2|[kb kk] len fc|[kb kk] len];
try reflexivity; crush.
Qed.
Definition XOK (bc : bctx) (X : ptree (option bx)) : Prop := forall bid, BXOK bc (xget X bid).
Lemma verdictF_eq : ltac2:(TCodec.tc2 tcn__FxCarry "Q7'R4'?'UH%211%411'T;'Q0'C'N%2211%911'G'8&ZK&XNr6r5%3221r4&VL(B%>2?;r3%34A=51r2r1%64BB21%746B41%911%@3<;1&TE%12?4%E3D31pj4I1pj:J1pmNI1ph>N1po8Q01ph4Q21").
Proof.
intros X sx b obr glo ghi. unfold verdictF, verdict, mk_sxi, gq_of. cbn [si_sx si_ab].
destruct (Pos.eqb b (sx_bid sx)); [reflexivity|].
destruct (sp_rng (sx_sp sx)) as [[lo1 hi1]|]; [|reflexivity].
destruct obr as [[lo2 hi2]|]; [|reflexivity].
destruct (Z.leb_spec (hi1 + a_off (sx_a sx) + sx_m1 sx) (glo + lo2));
destruct (Z.leb_spec (hi1 + a_off (sx_a sx) + sx_m1 sx - lo2) glo); try lia;
destruct (Z.leb_spec (ghi + hi2) (lo1 + a_off (sx_a sx)));
destruct (Z.leb_spec ghi (lo1 + a_off (sx_a sx) - hi2)); try lia; reflexivity.
Qed.
Lemma prune1pBF_eq : ltac2:(TCodec.tc2 tcn__FxCarry "J'G'RM'R<'R5'='QJ'QL'<'8%211'C%415'R7%611%4231%5216pk271pRL;1poN=1poJ?1poLA1po6C1phFE1&YA&T5%I3321").
Proof. fe. unfold prune1pBF, prune1pB. rewrite zmod64_fe. reflexivity. Qed.
Lemma prune1pcBF_eq : ltac2:(TCodec.tc2 tcn__FxCarry "O'G'RM'R<'R5'='QJ'QL'<'8%211'?'C'N%2211%411%819'R7%:11%7231%821:phN61pk2<1pRL@1poNB1poJD1poLF1po6H1phFJ1&YB&T6%N3321").
Proof. fe. unfold prune1pcBF, prune1pcB. rewrite prune1pBF_eq. reflexivity. Qed.
Lemma g1cBF_eq : ltac2:(TCodec.tc2 tcn__FxCarry "<'G'RM'T;'QL'<%112pRL31po851phF71&VC&S:%;3321").
Proof. fe. unfold g1cBF, g1cB. rewrite prune1pcBF_eq. reflexivity. Qed.
Lemma match_nz : forall (T : Type) (e : expr) (X Y : T),
match e with ELit 0 => false | _ => true end = true -> match e with ELit 0 => X | _ => Y end = Y.
Proof. intros T e X Y H. destruct e as [z| | | | | | |]; try reflexivity. destruct z; [discriminate|reflexivity|reflexivity]. Qed.
Lemma g1cBF_img_keep : forall bc sx lo hi lo1 hi1,
sp_rng (sx_sp sx) = Some (lo1, hi1) -> match a_base (sx_a sx) with ELit 0 => false | _ => true end = true ->
(if (if Z.leb 0 (hi - lo) then Z.ltb (hi - lo) two64 else false)
then (if Z.leb (hi1 + a_off (sx_a sx) + sx_m1 sx) lo then true else Z.leb hi (lo1 + a_off (sx_a sx))) else false) = true ->
g1cBF bc sx (KImg lo hi) = [KImg lo hi].
Proof.
intros bc sx lo hi lo1 hi1 Hsp Hnz HC.
destruct (Z.leb_spec 0 (hi - lo)) as [H0|H0]; [|discriminate]. destruct (Z.ltb_spec (hi - lo) two64) as [H1|H1]; [|discriminate].
assert (Hz : zlit64 (hi - lo) = hi - lo)
by (unfold zlit64; destruct (Z.leb_spec 0 (hi - lo)), (Z.ltb_spec (hi - lo) two64); cbn [andb]; first [reflexivity | lia]).
assert (HAP : ranges_apart_pB bc (sx_sp sx) (a_base (sx_a sx)) (a_off (sx_a sx)) (elen (sx_w sx)) (ELit 0) lo (ELit (hi - lo)) = true).
{ unfold ranges_apart_pB. cbn [elen base_rangeB]. rewrite Hsp. change (0 mod two64) with 0. cbv zeta. rewrite Hz. unfold sx_m1 in HC.
rewrite ?Z.add_0_l. replace (lo + (hi - lo)) with hi by lia.
destruct (Z.leb (hi1 + a_off (sx_a sx) + zlit64 (Z.of_nat (sx_w sx))) lo) eqn:EA; cbn [orb]; [reflexivity|].
rewrite HC. reflexivity. }
unfold g1cBF, prune1pcBF, prune1pBF. cbn [obrB kbase]. rewrite (match_nz _ _ _ _ Hnz).
replace (Z.ltb (hi - lo) two64) with true by (symmetry; apply Z.ltb_lt; exact H1). cbv zeta. cbn [a_base a_off]. rewrite HAP. reflexivity.
Qed.
Lemma g1cF_eq : ltac2:(TCodec.tc2 tcn__FxCarry "I'RM'R4'?'UH%211%411'T;'G'QL'<%112pRL31&VDr3&XNr2r1%3221%6251&VC%1274%>3:31po8@1ph4B1phFH1").
Proof.
intros bc X sx. fe. rename x into K. unfold g1cF. cbn [si_sx si_ab mk_sxi].
destruct K as [a w' v|a len|a len bk|lo hi|e' m'|e' lo' hi'|a en|c1 m1 c2 m2|a len fc|a len]; try reflexivity.
destruct (sp_rng (sx_sp sx)) as [[lo1 hi1]|] eqn:Hsp; cbv beta iota.
- destruct (match a_base (sx_a sx) with ELit 0 => false | _ => true end) eqn:Hnz.
+ set (C := if (if Z.leb 0 (hi - lo) then Z.ltb (hi - lo) two64 else false)
then (if Z.leb (hi1 + a_off (sx_a sx) + sx_m1 sx) lo then true else Z.leb hi (lo1 + a_off (sx_a sx))) else false).
assert (HK : (if C then [KImg lo hi] else g1cBF bc sx (KImg lo hi)) = g1cBF bc sx (KImg lo hi)).
{ destruct C eqn:EC; [|reflexivity]. symmetry. apply (g1cBF_img_keep bc sx lo hi lo1 hi1 Hsp Hnz EC). }
destruct (a_base (sx_a sx)) as [z| | | | | | |]; try exact HK. destruct z; [discriminate|exact HK|exact HK].
+ destruct (a_base (sx_a sx)) as [z| | | | | | |]; try discriminate. destruct z; [reflexivity|discriminate|discriminate].
- destruct (a_base (sx_a sx)) as [z| | | | | | |]; try reflexivity. destruct z; reflexivity.
Qed.
Lemma chain_slowF_eq : ltac2:(TCodec.tc2 tcn__FxCarry "M'RM'R4'?'UH%211%411'<'T;%211'G'QL%511pl>11&V6r3&M'ZI&XNr2%211r1%64>521%9281&S4%12:4%@3=31po:B1ph4F1phFL1").
Proof.
intros bc X sxs. induction sxs as [|sx rest IH]; fe; [reflexivity|].
cbn [map chain_slowF chain_slow]. rewrite g1cF_eq, g1cBF_eq, IH. reflexivity.
Qed.
Lemma chainK2F_eq : ltac2:(TCodec.tc2 tcn__FxCarry "QA'RM'R4'?'UH%211%411'<'T;%211&UAr4r3%3221&TLr5%2214'G'QL'QJ%A11'Q0'8p021'C'N%2211%H11%E1:phN21pnD71pn0;1pRL>1&V0r6&M'ZI&XN%11G%44O31K%736M1&S2%128N%J3;31p0L1p0Q01po:Q51pQP2Q:1ph4Q:1phFQ@1").
Proof.
intros bc X xo sxs HX Hxo. induction sxs as [|sx rest IH]; fe; [reflexivity|].
rename x into K, x0 into okb, x1 into same_of, x2 into br2.
cbn [map chainK2F chainK2 si_sx si_bx mk_sxi]. rewrite (prune1pcKF_eq bc (xget X (sx_bid sx)) xo (HX (sx_bid sx)) Hxo).
rewrite IH, chain_slowF_eq. reflexivity.
Qed.
Lemma chainKFF_eq : ltac2:(TCodec.tc2 tcn__FxCarry "S7'RM'R4'?'UH%211%411'Q0'C'N%2211%811'VN%:11'<'T;%211'QL'QJ%@11'8pQP0>1&UAr=r<%3221&TLr>%2214'G&WMr@&XNr?r1%3221r;r:r9%9784@?321(E%<3E21'T4&T7rA&TBr2%211&T>%113&TD%115&TC%117r8r6&T?%11;%311r5%A8@=;97621(RG%Q13D21p0F1po8QA1%QC1Q@&V2&X8&VL(B%QN2QOQK%24R0QLQ@Q?%34QOQOQ4Q3%443QO21%611&M'ZI%Q=1Q<%34QO21H%<8Q@QH5QGQ;Q:Q91r7r4%@7QCQG32KG1&S3&SK%12<O%36QG16OK5%QJ3F51p0H1p0QM1p0R11phNR@1pnDR71pn0R:1pRLR=1po:R?1pjJRC1pj4RH1pj:RI1pmNRH1ph>RM1pQP2S01ph4S01phFS61").
Proof.
intros bc X xo b obr glo ghi gx sxs K okb same_of br2 HX Hxo HS.
induction sxs as [|sx rest IH]; [reflexivity|].
cbn [map mk_flF mk_fl]. rewrite verdictF_eq.
destruct (verdict sx (b, obr, (glo, ghi))); [exact IH|].
destruct (linV bc (mk_sxi X sx) b obr glo ghi gx) eqn:EL.
- cbn [chainKF]. rewrite (HS sx EL). exact IH.
- cbn [chainKFF chainKF si_sx si_bx mk_sxi]. rewrite (prune1pcKF_eq bc (xget X (sx_bid sx)) xo (HX (sx_bid sx)) Hxo).
rewrite (chainK2F_eq bc X xo rest HX Hxo), chain_slowF_eq.
destruct (prune1pcK bc (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) K (same_of (sx_bid sx)) br2); [exact IH|reflexivity].
Qed.
Lemma obr_eqb_eq : ltac2:(TCodec.tc2 tcn__FxCarry "B'?'C'N%2211%411'G'8&T2r2r1%3221(E%73621r3%93:16p031ph><1ph6=1").
Proof.
intros [[x1 y1]|] [[x2 y2]|]; cbn [obr_eqb]; try discriminate; [|reflexivity].
intros H. apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1. apply Z.eqb_eq in H2. subst. reflexivity.
Qed.
Lemma linV_keep : forall bc X sx b obr glo ghi x K ei,
XOK bc X -> BXOK bc (gx_bx x) -> is_litb (gx_b x) = false ->
member_ok K (b, obr, (glo, ghi)) (Some x) = true -> inb (b, obr, (glo, ghi)) ei = true ->
linV bc (mk_sxi X sx) b obr glo ghi (Some x) = true ->
prune1pcK bc (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) K
(match kbase K with Some _ => Pos.eqb (ei_bid ei) | None => fun _ => false end (sx_bid sx))
(match kbase K with Some _ => ei_br ei | None => None end) = PKeep.
Proof.
intros bc X sx b obr glo ghi x K ei HX Hx Hlit HM Hinb HL.
unfold member_ok in HM. destruct (kdescr K) as [[[kb kk] [m|]]|] eqn:HD; try discriminate.
destruct (expr_eqb kb (gx_b x)) eqn:Eb; [|discriminate]. apply p_expr_eqb_eq in Eb. subst kb.
destruct (Z.leb_spec glo kk); [|discriminate]. apply Z.leb_le in HM.
unfold inb in Hinb. cbn [ei_m] in Hinb. destruct (ei_m ei) as [m'|]; [|discriminate].
apply andb_prop in Hinb as [Hinb _]. apply andb_prop in Hinb as [Hinb _]. apply andb_prop in Hinb as [Hb Hbr].
apply Pos.eqb_eq in Hb. apply obr_eqb_eq in Hbr. subst b obr.
unfold linV in HL. cbn [si_sx si_bx mk_sxi] in HL.
destruct (Pos.eqb (ei_bid ei) (sx_bid sx)) eqn:Ebid; [discriminate|].
destruct (if Z.leb 0 (ghi - glo) then Z.ltb (ghi - glo) two63z else false) eqn:Eg; [|discriminate].
assert (Hg : 0 <= ghi - glo < two63z) by (destruct (Z.leb_spec 0 (ghi - glo)); [destruct (Z.ltb_spec (ghi - glo) two63z); [lia|discriminate]|discriminate]).
rewrite (ranges_apart_pcF_eq bc _ _ (HX (sx_bid sx)) Hx) in HL.
assert (Hkb : forall z, gx_b x <> ELit z) by (intros z E; rewrite E in Hlit; discriminate).
destruct (kbase K) as [kb'|] eqn:HK.
- rewrite Ebid. apply (prune1pcK_keep_lin bc (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) K (gx_b x) kk m (ei_br ei) glo ghi); assumption.
- exfalso. destruct (kdescr_kbase K (gx_b x) kk (Some m) HD) as [HK'|(lo & hi & _ & E & _)]; [rewrite HK in HK'; discriminate|].
exact (Hkb 0 E).
Qed.
Lemma chainK2_fact : ltac2:(TCodec.tc2 tcn__FxCarry "Q9'RM'<'T;%211'QL'?'QJ%211'Q0'8p021'C'N%2211%911'G&W?r4%211(E%53;21%D1A&S2r7r6r5r3r2%66543;21(9(>%11K%33L71%B3<51p0>1phNE1pnDJ1pn0N1pRLQ21po:Q41phFQ81").
Proof.
intros bc sxs K okb same_of br2 HK. induction sxs as [|sx rest IH]; [reflexivity|].
cbn [chainK2]. replace (prune1pcK bc (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) K (same_of (sx_bid sx)) br2) with PKeep; [exact IH|].
destruct K; try discriminate; reflexivity.
Qed.
Lemma entriesGF_eq : ltac2:(TCodec.tc2 tcn__FxCarry "QA'RM'R4'?'UH%211%411'<'T;%211'RN%911&S@'QL%711'S7%=11%:11&UAr7r6%3221'G&V?r8&M'ZI&XN%119%44E319&X;r5r4%3592>14r3r2%=6<A7321&S8&SL%127C%35@D165%C3K51p0E1pk>J1pl8N1phLQ11pk<Q31po:Q61ph4Q:1phFQ@1").
Proof.
intros bc X sxs info bnds kn. induction kn as [|K rest IH]; intros infos HX; [reflexivity|].
destruct infos as [|oi irest]; [reflexivity|].
cbn [entriesGF entriesG]. rewrite (IH irest HX). f_equal.
assert (HN : BXOK bc None) by (intros x H; discriminate).
destruct oi as [ei|].
- rewrite (chainK2F_eq bc X (xget X (ei_bid ei)) sxs HX (HX (ei_bid ei))).
unfold mk_glF, mk_gl. rewrite !pt_get_map.
destruct (pt_get bnds (ei_gid ei)) as [[[b obr] [glo ghi]]|]; [|reflexivity].
destruct (inb (b, obr, (glo, ghi)) ei) eqn:Hinb; [|reflexivity].
set (gx := match pt_get info b with
| Some bi => if is_litb (bi_base bi) then None else Some (GXI (bi_base bi) (xget X b))
| None => None
end).
assert (GX : match gx with Some x => BXOK bc (gx_bx x) /\ is_litb (gx_b x) = false | None => True end).
{ unfold gx. destruct (pt_get info b) as [bi|]; [|exact I]. destruct (is_litb (bi_base bi)) eqn:E; [exact I|].
split; [apply HX|exact E]. }
destruct (member_ok K (b, obr, (glo, ghi)) gx) eqn:HM.
+ apply chainKFF_eq; [exact HX|apply HX|].
intros sx HL. destruct gx as [x|]; [|discriminate]. destruct GX as [GX1 GX2].
exact (linV_keep bc X sx b obr glo ghi x K ei HX GX1 GX2 HM Hinb HL).
+ apply chainKFF_eq; [exact HX|apply HX|]. intros sx HL. discriminate.
- rewrite (chainK2F_eq bc X None sxs HX HN).
destruct (is_fact_entry K) eqn:HK; [|reflexivity]. symmetry. apply chainK2_fact. exact HK.
Qed.
Lemma stores_partF_eq : ltac2:(TCodec.tc2 tcn__FxCarry "O'RM'R4'?'UH%211%411'<'T;%211&UAr3r2%3221'G'QL%911&ZDr4&M'ZI&XN%11;%44?31;%7261&T:%128>%=3;31p0?1po:D1ph4H1phFN1").
Proof.
intros bc X sxs HX. induction sxs as [|sx rest IH]; [reflexivity|].
cbn [map stores_partF stores_part si_sx si_bx mk_sxi]. rewrite IH, (chainK2F_eq bc X (xget X (sx_bid sx)) rest HX (HX (sx_bid sx))).
reflexivity.
Qed.
Lemma XOK_map : forall bc (P : binfo -> bool) t,
XOK bc (pt_map (fun bi => if P bi then Some (mk_bx bc (bi_base bi)) else None) t).
Proof.
intros bc P t bid x. unfold xget. rewrite pt_get_map.
destruct (pt_get t bid) as [bi|]; [|discriminate].
destruct (P bi); [|discriminate]. intros H. injection H as <-. reflexivity.
Qed.
Lemma disj_sidesB_filter : ltac2:(TCodec.tc2 tcn__FxCarry "L'RM'<'QL%211'QJ'N'G'C'R5%2215%911&S5r5&[?&W@r4%33>21r3r2r1%9584321%:596432%@3<21pm<B1pkJC1phBE1pl8G1phFK1").
Proof. intros bc kn b1 k1 n1. induction kn as [|K rest IH]; [reflexivity|]. destruct K; cbn [List.filter is_kdisjb disj_sidesB]; rewrite ?IH; reflexivity. Qed.
Lemma disj_sides_xB_filter : ltac2:(TCodec.tc2 tcn__FxCarry "L'RM'<'QL%211'QJ'N'G'C'R5%2215%911&S6r5&[?&W@r4%33>21r3r2r1%9584321%:596432%@3<21pm<C1pkJC1phBE1pl8G1phFK1").
Proof. intros bc kn b1 k1 n1. induction kn as [|K rest IH]; [reflexivity|]. destruct K; cbn [List.filter is_kdisjb disj_sides_xB]; rewrite ?IH; reflexivity. Qed.
Lemma disj_both_eq : ltac2:(TCodec.tc2 tcn__FxCarry "Q>'RM'<'QL%211'QJ'N'G'8&7&[Fzr1%3221&[H&R>%2241%8241(E%<3;21'C'R5%221A%E11%4211&V7r6r5r4r3r2%6554321(B&S5%1587654&S6(QB%117%35<;:91%74@@51%Q13@91p0F1pm<Q41pkJQ51phBQ71pl8Q91phFQ=1").
Proof.
intros bc kn b1 k1 n1 Hn. induction kn as [|K rest IH]; [reflexivity|].
destruct K; cbn [disj_both disj_sidesB disj_sides_xB]; rewrite ?IH; try reflexivity.
unfold sub_itvB, sub_itv_xB, num_sub. rewrite Hn. cbv [andb]. reflexivity.
Qed.
Lemma zlit64_range : ltac2:(TCodec.tc2 tcn__FxCarry "A'N'G'8&7&[Fz&RBr1%211%5241&[H&R>%2241%:241(E%>3=21pQP6@1").
Proof.
intros z. pose proof (Z.mod_pos_bound z two64 ltac:(unfold two64; lia)) as B. unfold zlit64.
destruct (Z.leb_spec 0 z); destruct (Z.ltb_spec z two64); cbn [andb];
apply andb_true_intro; split; first [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.
Lemma mk_sprepF_eq : ltac2:(TCodec.tc2 tcn__FxCarry "F'RM'QJ'N'G'R<&XIr4&UC&X6%113%311r3r2r1%9584321&SM%14:543%>3=31pm<A1pkJA1phBC1phFE1").
Proof.
intros bc b1 k1 n1. unfold mk_sprepF, mk_sprepB. cbn [be_kd mk_bext].
destruct n1; rewrite ?disj_sides_xB_filter; try reflexivity.
rewrite disj_sidesB_filter. destruct (Z.eqb (zlit64 z) z) eqn:E; [|reflexivity].
apply Z.eqb_eq in E. rewrite disj_both_eq by (rewrite <- E; apply zlit64_range).
rewrite disj_sidesB_filter, disj_sides_xB_filter, E. reflexivity.
Qed.
Lemma mk_stxsF_eq : ltac2:(TCodec.tc2 tcn__FxCarry "I'RM'<'R6%211'T1'G'C'T;%711%3215&XLr3&UC&X6%113%311r2r1%847321&SN%13943%@3<31po<B1plLD1phFH1").
Proof.
intros bc log t. induction log as [|[a w v] older IH]; [reflexivity|].
cbn [mk_stxsF mk_stxs]. rewrite IH. destruct (mk_stxs bc older t) as [sxs t1].
destruct (intern bc t1 (a_base a)) as [[bid bi] t2]. rewrite mk_sprepF_eq. reflexivity.
Qed.
Lemma carryGF_eq : ltac2:(TCodec.tc2 tcn__FxCarry "='G'RM'<'R6%211'QL%411pl811plL41phF81&UJ&S0%<3321").
Proof.
fe. rename x into bc, x0 into log, x1 into kn. unfold carryGF, carryG. rewrite mk_stxsF_eq.
destruct (mk_stxs bc log nt_empty) as [sxs t0].
destruct (scan_entries bc kn t0 gst_empty) as [[infos t1] gs].
rewrite stores_partF_eq, entriesGF_eq; [reflexivity| apply XOK_map | apply XOK_map].
Qed.
Lemma carryKF1_eq : ltac2:(TCodec.tc2 tcn__FxCarry "E'G'RM'<'R6%211'QL%411'8%611'C'R7%911%3261%4215pk261pl891plL<1phF@1&UN&S1%D3321").
Proof. fe. unfold carryKF1, carryK. rewrite carryGF_eq. reflexivity. Qed.
Definition nov (kk l0 k : Z) (w : nat) : bool :=
if Z.ltb 0 l0 then if Z.ltb l0 two64 then (if Z.leb (kk + l0) k then true else Z.leb (k + Z.of_nat w) kk) else false else false.
Definition img_nov (lo hi k : Z) (w : nat) : bool :=
if Z.ltb lo hi then (if Z.leb hi k then true else Z.leb (k + Z.of_nat w) lo) else false.
Definition ranges_apart_pcS (bc : bctx) (sp : sprep) (b1 : expr) (k1 : Z) (z1 : Z)
(br2 : option (Z * Z)) (b2 : expr) (k2 : Z) (n2 : expr) (h2o e2o : option Z) : bool :=
if (match sp_rng sp, br2, sp_h1 sp, h2o with
| Some (lo1, hi1), Some (lo2, hi2), Some h1, Some h2 =>
if Z.leb (hi1 + k1 + h1) (lo2 + k2) then true else if Z.leb (hi2 + k2 + h2) (lo1 + k1) then true
else match e2o with Some e2 => Z.leb e2 (lo1 + k1) | None => false end
| _, _, _, _ => false
end) then true
else if in_sides_xB bc (sp_Dx sp) b2 k2 n2 then true
else if shares_var b1 b2 then
(if lin_ge0B bc [(b2, k2)] [(b1, k1); (ELit z1, 0)] then true else lin_ge0B bc [(b1, k1)] [(b2, k2); (n2, 0)])
else false.
Definition mk_pre (bc : bctx) (K : kentry) (br2 : option (Z * Z)) : option Z * option Z :=
match K with
| KZero (SA kb kk) len | KFill (SA kb kk) len _ | KUnk (SA kb kk) len | KBlob (SA kb kk) len _ =>
let h2o := xhiB bc len in
(h2o, match br2, h2o with Some (lo2, hi2), Some h2 => end_hiB bc kb kk len lo2 hi2 h2 | _, _ => None end)
| _ => (None, None)
end.
Definition fastkeep (K : kentry) (wa : saddr) (w : nat) (same : bool) : bool :=
match K with
| KZero (SA _ kk) (ELit l0) | KFill (SA _ kk) (ELit l0) _ | KUnk (SA _ kk) (ELit l0) => if same then nov kk l0 (a_off wa) w else false
| KImg lo hi => match a_base wa with ELit 0 => img_nov lo hi (a_off wa) w | _ => false end
| _ => false
end.
Definition prune1pcKS (bc : bctx) (sp : sprep) (wa : saddr) (w : nat) (wv : expr) (K : kentry) (same : bool)
(br2 : option (Z * Z)) (h2o e2o : option Z) : pk_res :=
let wb := a_base wa in let k := a_off wa in
if same then prune1pcKF bc None None sp wa w wv K same br2 else
match K with
| KZero (SA kb kk) len =>
match len with
| ELit _ => prune1pcKF bc None None sp wa w wv K same br2
| _ => if ranges_apart_pcS bc sp wb k (Z.of_nat w) br2 kb kk len h2o e2o then PKeep else PRepl (kcutB bc KZero wb k (elen w) kb kk len)
end
| KFill (SA kb kk) len c =>
match len with
| ELit _ => prune1pcKF bc None None sp wa w wv K same br2
| _ => if ranges_apart_pcS bc sp wb k (Z.of_nat w) br2 kb kk len h2o e2o then PKeep else PRepl (kcutB bc (fun a n => KFill a n c) wb k (elen w) kb kk len)
end
| KUnk (SA kb kk) len =>
match len with
| ELit _ => prune1pcKF bc None None sp wa w wv K same br2
| _ => if ranges_apart_pcS bc sp wb k (Z.of_nat w) br2 kb kk len h2o e2o then PKeep else PRepl (kcutB bc KUnk wb k (elen w) kb kk len)
end
| KBlob (SA kb kk) len _ =>
match len with
| ELit _ => prune1pcKF bc None None sp wa w wv K same br2
| _ => if ranges_apart_pcS bc sp wb k (Z.of_nat w) br2 kb kk len h2o e2o then PKeep else PRepl []
end
| _ => prune1pcKF bc None None sp wa w wv K same br2
end.
Definition prune1pcKF2 (bc : bctx) (i1 i2 : option bx) (sp : sprep) (wa : saddr) (w : nat) (wv : expr) (K : kentry) (same : bool)
(br2 : option (Z * Z)) (pre : option (option Z * option Z)) : pk_res :=
if fastkeep K wa w same then PKeep else
match pre with
| Some (h2o, e2o) => prune1pcKS bc sp wa w wv K same br2 h2o e2o
| None => prune1pcKF bc i1 i2 sp wa w wv K same br2
end.
Definition zlit64F (z : Z) : Z := if Z.leb 0 z then (if Z.ltb z two64 then z else zmod64 z) else zmod64 z.
Definition wlenF (w : nat) : Z :=
match w with
| 1%nat => 1 | 2%nat => 2 | 4%nat => 4 | 8%nat => 8
| _ => zlit64F (Z.of_nat w)
end.
Definition kdescrF (K : kentry) : option (expr * Z * option Z) :=
match K with
| KWord (SA kb kk) w _ => Some (kb, kk, Some (wlenF w))
| KZero (SA kb kk) len | KUnk (SA kb kk) len | KFill (SA kb kk) len _ | KBlob (SA kb kk) len _ =>
Some (kb, kk, match len with ELit z => Some (zlit64F z) | _ => None end)
| KImg lo hi => let d := hi - lo in Some (ELit 0%Z, lo, if Z.ltb d two64 then Some (zlit64F d) else None)
| _ => None
end.
Fixpoint shrn (n : nat) (p : positive) : positive :=
match n with O => p | S n' => match p with xH => xH | xO q => shrn n' q | xI q => shrn n' q end end.
Definition gkeyF (kk : Z) : positive :=
match kk with Z0 => xH | Zpos p => xI (shrn 16 p) | Zneg p => xO (shrn 16 p) end.
Definition ggroupK (gs : gst) (bid gk : positive) : positive * gst :=
let inner := match pt_get (gs_gid gs) bid with Some i => i | None => PTLeaf end in
match pt_get inner gk with
| Some gid => (gid, gs)
| None => let gid := gs_next gs in
(gid, GST (pt_set bid (pt_set gk gid inner) (gs_gid gs)) (Pos.succ gid) (gs_bnds gs))
end.
Definition ggroupF (gs : gst) (bid : positive) (kk : Z) : positive * gst := ggroupK gs bid (gkeyF kk).
Definition bnd_addF (gs : gst) (gid bid : positive) (obr : option (Z * Z)) (lo hi : Z) : gst :=
match pt_get (gs_bnds gs) gid with
| Some (b, o, (l, h)) =>
if Z.leb l lo then (if Z.leb hi h then gs else GST (gs_gid gs) (gs_next gs) (pt_set gid (b, o, (l, hi)) (gs_bnds gs)))
else GST (gs_gid gs) (gs_next gs) (pt_set gid (b, o, (lo, if Z.leb hi h then h else hi)) (gs_bnds gs))
| None => GST (gs_gid gs) (gs_next gs) (pt_set gid (bid, obr, (lo, hi)) (gs_bnds gs))
end.
Record einfoF := EF { ef_bid : positive; ef_gid : positive; ef_kb : expr; ef_br : option (Z * Z); ef_k : Z; ef_m : option Z; ef_end : Z }.
Definition ef_ei (e : einfoF) : einfo := EI (ef_bid e) (ef_gid e) (ef_kb e) (ef_br e) (ef_k e) (ef_m e).
Fixpoint scanF (bc : bctx) (kn : list kentry) (t : ntab) (gs : gst) : list (option einfoF) * ntab * gst :=
match kn with
| [] => ([], t, gs)
| K :: rest =>
match kdescrF K with
| Some (kb, kk, om) =>
let '(r, t1) := intern bc t kb in
let '(bid, bi) := r in
match om with
| Some m =>
let ke := kk + m in
let '(gid, gs0) := ggroupF gs bid kk in
let '(infos, t2, gs2) := scanF bc rest t1 (bnd_addF gs0 gid bid (bi_br bi) kk ke) in
(Some (EF bid gid kb (bi_br bi) kk om ke) :: infos, t2, gs2)
| None =>
let '(infos, t2, gs2) := scanF bc rest t1 gs in
(Some (EF bid xH kb (bi_br bi) kk om kk) :: infos, t2, gs2)
end
| None =>
let '(infos, t2, gs2) := scanF bc rest t gs in
(None :: infos, t2, gs2)
end
end.
Fixpoint alookupEF (l : list (expr * positive)) (b : expr) : option positive :=
match l with
| [] => None
| (b', id) :: rest => if expr_eqbF b b' then Some id else alookupEF rest b
end.
Lemma alookupEF_eq : ltac2:(TCodec.tc2 tcn__FxCarry "B'<'C'QJ'Q0%3221%511'G'?%115&UBr2r1%3221&RJ%1243%93731ph>>1pl><1").
Proof. induction l as [|[b' id] rest IH]; intros b; [reflexivity|]. cbn [alookupEF alookupE]. rewrite BLKF.expr_eqbF_eq, IH. reflexivity. Qed.
Fixpoint nth4 {A : Type} (n : nat) (l : list A) (d : A) {struct n} : A :=
match n with
| S (S (S (S m))) => match l with _ :: _ :: _ :: _ :: r => nth4 m r d | _ => nth n l d end
| _ => nth n l d
end.
Lemma nth4_eq : forall (A : Type) n (l : list A) d, nth4 n l d = nth n l d.
Proof.
intros A n. induction n as [n IH] using (well_founded_induction Wf_nat.lt_wf). intros l d.
destruct n as [|[|[|[|m]]]]; try reflexivity.
cbn [nth4]. destruct l as [|a [|b [|c [|e r]]]]; try reflexivity.
cbn [nth]. apply IH. repeat constructor.
Qed.
Definition internF (bc : bctx) (t : ntab) (b : expr) : positive * binfo * ntab :=
let k := bkey b in
match alookupEF (match k with Some n => nth4 n (nt_vars t) [] | None => nt_other t end) b with
| Some id => (id, match pt_get (nt_info t) id with Some bi => bi | None => BI b (base_rangeB bc b) end, t)
| None => let id := nt_next t in
let bi := BI b (base_rangeB bc b) in
(id, bi, nt_add t k (b, id) bi)
end.
Lemma internF_eq : ltac2:(TCodec.tc2 tcn__FxCarry "D'RM'T1'QJ'G'C'Q0'RN%3221%4217&W<r3r2r1%43321&SD%13543%=3831ph>?1po<A1phFC1").
Proof.
intros bc t b. unfold internF, intern, nt_bucket, lget. rewrite alookupEF_eq. destruct (bkey b); [rewrite nth4_eq|]; reflexivity.
Qed.
Definition intern_c (bc : bctx) (t : ntab) (lb : option (expr * positive * binfo)) (b : expr) : positive * binfo * ntab :=
match lb with
| Some (b', id, bi) => if expr_eqbF b b' then (id, bi, t) else internF bc t b
| None => internF bc t b
end.
Definition ggroup_c (gs : gst) (lg : option (positive * positive * positive)) (bid gk : positive) : positive * gst :=
match lg with
| Some (b', gk', gid) => if Pos.eqb bid b' then (if Pos.eqb gk gk' then (gid, gs) else ggroupK gs bid gk) else ggroupK gs bid gk
| None => ggroupK gs bid gk
end.
Fixpoint scanF2 (bc : bctx) (kn : list kentry) (t : ntab) (gs : gst) (lb : option (expr * positive * binfo))
(lg : option (positive * positive * positive)) : list (option einfoF) * ntab * gst :=
match kn with
| [] => ([], t, gs)
| K :: rest =>
match kdescrF K with
| Some (kb, kk, om) =>
let '(r, t1) := intern_c bc t lb kb in
let '(bid, bi) := r in
match om with
| Some m =>
let ke := kk + m in
let gk := gkeyF kk in
let '(gid, gs0) := ggroup_c gs lg bid gk in
let '(infos, t2, gs2) := scanF2 bc rest t1 (bnd_addF gs0 gid bid (bi_br bi) kk ke) (Some (kb, bid, bi)) (Some (bid, gk, gid)) in
(Some (EF bid gid kb (bi_br bi) kk om ke) :: infos, t2, gs2)
| None =>
let '(infos, t2, gs2) := scanF2 bc rest t1 gs (Some (kb, bid, bi)) lg in
(Some (EF bid xH kb (bi_br bi) kk om kk) :: infos, t2, gs2)
end
| None =>
let '(infos, t2, gs2) := scanF2 bc rest t gs lb lg in
(None :: infos, t2, gs2)
end
end.
Definition zfKF (bc : bctx) (i1 i2 : option bx) (sp : sprep) (wa : saddr) (w : nat) (same : bool) (br2 : option (Z * Z))
(mk : saddr -> expr -> kentry) (kb : expr) (kk : Z) (len : expr) : pk_res :=
let k := a_off wa in
let wb := a_base wa in
if same then
match len with
| ELit l0 => PRepl (ktrim mk kb kk l0 k w)
| _ => if Z.leb (k + Z.of_nat w) kk then PKeep else PRepl (kcutB bc mk wb k (elen w) kb kk len)
end
else if ranges_apart_pcF bc i1 i2 sp wb k (elen w) br2 kb kk len then PKeep
else PRepl (kcutB bc mk wb k (elen w) kb kk len).
Definition prune1pcKF3 (bc : bctx) (i1 i2 : option bx) (sp : sprep) (wa : saddr) (w : nat) (wv : expr) (K : kentry) (same : bool)
(br2 : option (Z * Z)) : pk_res :=
match K with
| KAlign _ _ | KRange _ _ _ | KWr _ _ | KDisj _ _ _ _ => PKeep
| KImg lo hi =>
let k := a_off wa in
match a_base wa with
| ELit 0 =>
let r1 := if Z.ltb lo (Z.min k hi) then [KImg lo (Z.min k hi)] else [] in
let lo2 := Z.max lo (k + Z.of_nat w) in
let r2 := if Z.ltb lo2 hi then [KImg lo2 hi] else [] in
PRepl (r1 ++ r2)
| wb => if Z.ltb (hi - lo) two64 then
(if ranges_apart_pB bc sp wb k (elen w) (ELit 0) lo (ELit (hi - lo)) then PKeep else PRepl [])
else PRepl []
end
| KZero (SA kb kk) len => zfKF bc i1 i2 sp wa w same br2 KZero kb kk len
| KFill (SA kb kk) len c => zfKF bc i1 i2 sp wa w same br2 (fun a n => KFill a n c) kb kk len
| KUnk (SA kb kk) len => zfKF bc i1 i2 sp wa w same br2 KUnk kb kk len
| KWord (SA kb kk) w' v =>
let k := a_off wa in
if same then (if Z.leb (kk + Z.of_nat w') k then PKeep else if Z.leb (k + Z.of_nat w) kk then PKeep else PRepl (kword_cut kb kk w' v k w))
else if ranges_apart_pcF bc i1 i2 sp (a_base wa) k (elen w) br2 kb kk (elen w') then PKeep
else if (if Nat.eqb w 1 then if Nat.eqb w' 1 then expr_eqb wv v else false else false) then PKeep
else PRepl []
| KBlob (SA kb kk) len bk =>
let k := a_off wa in
if same then
match len with
| ELit l0 => let l := zmod64 l0 in
if Z.leb (kk + l) k then PKeep else if Z.leb (k + Z.of_nat w) kk then PKeep else PRepl []
| _ => if Z.leb (k + Z.of_nat w) kk then PKeep else PRepl []
end
else if ranges_apart_pcF bc i1 i2 sp (a_base wa) k (elen w) br2 kb kk len then PKeep else PRepl []
end.
Definition nov2 (kk l0 k ke : Z) : bool :=
if Z.ltb 0 l0 then if Z.ltb l0 two64 then (if Z.leb (kk + l0) k then true else Z.leb ke kk) else false else false.
Definition prune1pcKF2' (bc : bctx) (i1 i2 : option bx) (sp : sprep) (wa : saddr) (w : nat) (wv : expr) (K : kentry) (same : bool)
(br2 : option (Z * Z)) (pre : option (option Z * option Z)) : pk_res :=
if fastkeep K wa w same then PKeep else
match pre with
| Some (h2o, e2o) => prune1pcKS bc sp wa w wv K same br2 h2o e2o
| None => prune1pcKF3 bc i1 i2 sp wa w wv K same br2
end.
Definition prune1pcKX (bc : bctx) (si : sxi) (i2 : option bx) (K : kentry) (same : bool)
(br2 : option (Z * Z)) (pre : option (option Z * option Z)) : pk_res :=
let sx := si_sx si in
match K with
| KWord (SA kb kk) w' v =>
if same then (let k := a_off (sx_a sx) in if Z.leb (kk + Z.of_nat w') k then PKeep else if Z.leb (si_ke si) kk then PKeep else PRepl (kword_cut kb kk w' v k (sx_w sx)))
else prune1pcKF2' bc (si_bx si) i2 (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) K same br2 pre
| KZero (SA kb kk) (ELit l0) | KFill (SA kb kk) (ELit l0) _ | KUnk (SA kb kk) (ELit l0) =>
if same then (if nov2 kk l0 (a_off (sx_a sx)) (si_ke si) then PKeep else prune1pcKF2' bc (si_bx si) i2 (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) K same br2 pre)
else prune1pcKF2' bc (si_bx si) i2 (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) K same br2 pre
| KImg lo hi =>
match a_base (sx_a sx) with
| ELit 0 => if (if Z.ltb lo hi then (if Z.leb hi (a_off (sx_a sx)) then true else Z.leb (si_ke si) lo) else false) then PKeep
else prune1pcKF2' bc (si_bx si) i2 (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) K same br2 pre
| _ => prune1pcKF2' bc (si_bx si) i2 (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) K same br2 pre
end
| _ => prune1pcKF2' bc (si_bx si) i2 (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) K same br2 pre
end.
Fixpoint chainK2F2 (bc : bctx) (xo : option bx) (sis : list sxi) (K : kentry) (okb : option expr) (same_of : positive -> bool)
(br2 : option (Z * Z)) (pre : option (option Z * option Z)) : list kentry :=
match sis with
| [] => [K]
| si :: rest =>
let sx := si_sx si in
match prune1pcKX bc si xo K (same_of (sx_bid sx)) br2 pre with
| PKeep => chainK2F2 bc xo rest K okb same_of br2 pre
| PRepl l =>
match okb with
| Some kb =>
flat_map (fun K' => match kbase K' with
| Some kb' => if expr_eqb kb' kb then chainK2F2 bc xo rest K' okb same_of br2 None else chain_slowF bc rest [K']
| None => chain_slowF bc rest [K']
end) l
| None => chain_slowF bc rest l
end
end
end.
Fixpoint chainKFF2 (bc : bctx) (xo : option bx) (fl : list (sxi * list sxi)) (K : kentry) (okb : option expr) (same_of : positive -> bool)
(br2 : option (Z * Z)) (pre : option (option Z * option Z)) : list kentry :=
match fl with
| [] => [K]
| (si, rest) :: fl' =>
let sx := si_sx si in
match prune1pcKX bc si xo K (same_of (sx_bid sx)) br2 pre with
| PKeep => chainKFF2 bc xo fl' K okb same_of br2 pre
| PRepl l =>
match okb with
| Some kb =>
flat_map (fun K' => match kbase K' with
| Some kb' => if expr_eqb kb' kb then chainK2F2 bc xo rest K' okb same_of br2 None else chain_slowF bc rest [K']
| None => chain_slowF bc rest [K']
end) l
| None => chain_slowF bc rest l
end
end
end.
Fixpoint mk_flG (skip : sxi -> bool) (sis : list sxi) : list (sxi * list sxi) :=
match sis with
| si :: srest => if skip si then mk_flG skip srest else (si, srest) :: mk_flG skip srest
| [] => []
end.
Fixpoint in_sides_num (bc : bctx) (D : list (saddr * expr)) (b : expr) (k n : Z) : bool :=
match D with
| [] => false
| (c, m) :: r => if num_sub bc b k n c m then true else in_sides_num bc r b k n
end.
Definition linV2 (bc : bctx) (si : sxi) (b : positive) (glo ghi : Z) (gx : option gxi) : bool :=
match gx with
| Some x =>
if Pos.eqb b (sx_bid (si_sx si)) then false else
if (if Z.leb 0 (ghi - glo) then Z.ltb (ghi - glo) two63z else false) then
let sx := si_sx si in
if in_sides_num bc (sp_D (sx_sp sx)) (gx_b x) glo (ghi - glo) then true
else if lin_apartF bc (si_bx si) (gx_bx x) (a_base (sx_a sx)) (a_off (sx_a sx)) (zlit64F (Z.of_nat (sx_w sx))) (gx_b x) glo (ghi - glo) then true
else in_sidesB bc (sp_D (sx_sp sx)) (gx_b x) glo (ghi - glo)
else false
| None => false
end.
Definition gflF2 : Type := (positive * Z * Z * list (sxi * list sxi))%type.
Definition eni_of2 (K : kentry) (br2 : option (Z * Z)) (h2o e2o : option Z) : option (PrimInt63.int * PrimInt63.int * option PrimInt63.int) :=
match K with
| KZero (SA _ kk) len | KFill (SA _ kk) len _ | KUnk (SA _ kk) len | KBlob (SA _ kk) len _ =>
match len with
| ELit _ => None
| _ =>
match br2, h2o with
| Some (lo2, hi2), Some h2 =>
match z2i (lo2 + kk), z2i (hi2 + kk + h2) with
| Some el, Some eh =>
match e2o with
| None => Some (el, eh, None)
| Some e2 => match z2i e2 with Some i => Some (el, eh, Some i) | None => None end
end
| _, _ => None
end
| _, _ => None
end
end
| _ => None
end.
Fixpoint stores_partF2 (bc : bctx) (sis : list sxi) : list kentry :=
match sis with
| [] => []
| si :: newer => let sx := si_sx si in
stores_partF2 bc newer ++ chainK2F2 bc (si_bx si) newer (KWord (sx_a sx) (sx_w sx) (sx_v sx)) (Some (a_base (sx_a sx))) (Pos.eqb (sx_bid sx)) (sx_br sx) None
end.
Definition mk_sctx (bc : bctx) (ex : bext) (s : sentry) : sprep :=
match s with SE a w v => mk_sprepF bc (be_kd ex) (a_base a) (a_off a) (elen w) end.
Definition intern_r (t : ntab) (b : expr) (br : option (Z * Z)) : positive * binfo * ntab :=
let k := bkey b in
match alookupEF (match k with Some n => nth4 n (nt_vars t) [] | None => nt_other t end) b with
| Some id => (id, match pt_get (nt_info t) id with Some bi => bi | None => BI b br end, t)
| None => let id := nt_next t in
let bi := BI b br in
(id, bi, nt_add t k (b, id) bi)
end.
Lemma intern_r_eq : ltac2:(TCodec.tc2 tcn__FxCarry "F'RM'T1'QJ'G'C'Q0'RN%3221%4217&W>r2r1&RKr3%2213%63541&SD%13476%?3:31ph>A1po<C1phFE1").
Proof.
intros bc t b. unfold intern_r, intern, nt_bucket, lget. rewrite alookupEF_eq. destruct (bkey b); [rewrite nth4_eq|]; reflexivity.
Qed.
Fixpoint mk_stxsC2 (log : list sentry) (scs : list sprep) (t : ntab) : list stx * ntab :=
match log, scs with
| SE a w v :: older, sp :: scs' =>
let '(sxs, t1) := mk_stxsC2 older scs' t in
let '(r, t2) := intern_r t1 (a_base a) (sp_rng sp) in
let '(bid, bi) := r in
(sxs ++ [STX a w v sp bid (bi_br bi)], t2)
| _, _ => ([], t)
end.
Lemma mk_stxs_okG : ltac2:(TCodec.tc2 tcn__FxCarry "QF'RM'<'R6%211'T1'T;%511&RFr5r3%3221'G'C%1279&SNr6r4%33291(Br2%24>@;1%:3841'Fr7%A21?'L&RI%124B%33G1<'?'=%211'QJ'Q0%F221&[>r1&SO%12?C%43531%32IO%637F1p031pn291pkF=1%G2A1%H2F1p0J1p0Q61po>Q=1po:Q<1po<Q?1plLQA1phFQE1").
Proof.
intros bc log. induction log as [|[a w v] older IH]; intros t sxs t' HT H.
- cbn in H. injection H as <- <-. split; [exact HT|]. split; [constructor|]. intros; assumption.
- cbn [mk_stxs] in H. destruct (mk_stxs bc older t) as [sxs0 t1] eqn:E0.
destruct (intern bc t1 (a_base a)) as [[bid bi] t2] eqn:EI.
injection H as <- <-.
destruct (IH t sxs0 t1 HT E0) as (HT1 & HS & Hm1).
destruct (intern_ok _ _ _ _ _ _ HT1 EI) as (HT2 & -> & HIn & Hm2).
split; [exact HT2|]. split.
+ apply Forall_app. split.
* apply Forall_impl with (P := SX_OK bc t1); [|exact HS]. intros sx. apply SX_OK_mono. exact Hm2.
* constructor; [|constructor]. split; [exact HIn|]. split; reflexivity.
+ intros k p Hp. apply Hm2. apply Hm1. exact Hp.
Qed.
Lemma scan_entries_okG : ltac2:(TCodec.tc2 tcn__FxCarry "QN'RM'<'QL%211'T1'S>'?'S7%211%811&RFr7r5%3221'G'C%127<%221<&T9r8r6%342:19(Br4r3%34@E21r2%54;F21%>3;71'Fr9%E218'=%K11'QJ'Q0%E221&[>r1&SO%12:>%43531%32OB%637A1p031pn291pkF=1'[=&RE%12CJ%35Q@Q:1OQ6%F251%G2E1p0I1p0Q91pjBQB1po>QD1pk>Q@1pj@QE1po<QG1pl8QI1phFQM1").
Proof.
intros bc kn. induction kn as [|K rest IH]; intros t gs infos t' gs' HT H.
- cbn in H. injection H as <- <- <-. split; [exact HT|]. split; [intros; assumption|]. constructor.
- cbn [scan_entries] in H.
destruct (kdescr K) as [[[kb kk] om]|] eqn:HD.
+ destruct (intern bc t kb) as [[bid bi] t1] eqn:EI.
destruct (intern_ok _ _ _ _ _ _ HT EI) as (HT1 & Hbi & HIn & Hm1).
lazymatch type of H with (let '(_, _) := ?X in _) = _ => destruct X as [gid gs1] end.
destruct (scan_entries bc rest t1 _) as [[infos2 t2] gs2] eqn:ES.
injection H as <- <- <-.
destruct (IH _ _ _ _ _ HT1 ES) as (HT2 & Hm2 & HF).
split; [exact HT2|]. split; [intros k p Hp; apply Hm2; apply Hm1; exact Hp|].
constructor; [|exact HF]. cbn [EINF ei_kb ei_k ei_m ei_bid ei_br].
split; [exact HD|]. split; [apply Hm2; exact HIn|]. rewrite Hbi. reflexivity.
+ destruct (scan_entries bc rest t gs) as [[infos2 t2] gs2] eqn:ES.
injection H as <- <- <-.
destruct (IH _ _ _ _ _ HT ES) as (HT2 & Hm2 & HF).
split; [exact HT2|]. split; [exact Hm2|]. constructor; [exact HD | exact HF].
Qed.
Lemma verdict_keepG : forall bc t sx g ei K,
NTI bc t -> SX_OK bc t sx -> EINF bc t K (Some ei) -> inb g ei = true -> verdict sx g = true ->
prune1pcK bc (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) K
(match kbase K with Some _ => Pos.eqb (ei_bid ei) | None => fun _ => false end (sx_bid sx))
(match kbase K with Some _ => ei_br ei | None => None end) = PKeep.
Proof.
intros bc t sx g ei K HT HSX HK Hinb Hv. cbn [EINF] in HK. destruct HK as (HD & HIn & Hbr).
assert (Hm : exists m, ei_m ei = Some m).
{ unfold inb in Hinb. destruct (ei_m ei) as [m|]; [exists m; reflexivity|discriminate]. }
destruct Hm as [m Hm].
destruct (verdict_inb_num _ _ _ _ Hv Hinb Hm) as (Hne & lo1 & hi1 & lo2 & hi2 & Hsp & Hbr2 & Hnum).
destruct HSX as (SXin & SXbr & SXsp).
rewrite Hm in HD.
destruct (kdescr_kbase _ _ _ _ HD) as [HB|(lo & hi & -> & Hkb & Hk)].
- rewrite HB. rewrite Hne. rewrite Hbr. eapply prune1pcK_keep_based; [exact HB|exact HD|exact Hsp| | exact Hnum].
rewrite <- Hbr. exact Hbr2.
- cbn [kbase]. rewrite Hkb, Hk in *.
eapply prune1pcK_keep_img; [exact HD| |exact Hsp| rewrite <- Hbr; exact Hbr2 | exact Hnum].
rewrite <- (nt_same_eq _ _ _ _ _ _ HT HIn SXin). exact Hne.
Qed.
Lemma two64_pow : ltac2:(TCodec.tc2 tcn__FxCarry "8'G'N&[M+2+R0%3221&R>%73621"). Proof. reflexivity. Qed.
Lemma ktrim_nov : ltac2:(TCodec.tc2 tcn__FxCarry "Q9'R5'QJ'QLp021p041'N'='G'8&Y8r4r3r2r1%544321(E%93821'<%11@&QMr7r6r5%46321=<;(9(QE%1254(QB%11B%9231(>%11M%83N31%J3?:1p0B1poJM1pkFO1pl@Q01pl4Q11pl0Q61pm6Q41").
Proof.
intros mk kb kk l0 k w H. unfold nov in H. unfold ktrim. rewrite two64_pow.
destruct (Z.ltb_spec 0 l0); [|discriminate]. destruct (Z.ltb_spec l0 two64); [|discriminate].
rewrite (Z.mod_small l0 two64) by lia.
destruct (Z.leb_spec (kk + l0) k).
- rewrite (Z.min_r k (kk + l0)) by lia. destruct (Z.ltb_spec kk (kk + l0)); [|lia].
destruct (Z.ltb_spec (Z.max kk (k + Z.of_nat w)) (kk + l0)); [lia|].
replace (kk + l0 - kk) with l0 by lia. reflexivity.
- apply Z.leb_le in H. rewrite (Z.min_l k (kk + l0)) by lia. destruct (Z.ltb_spec kk k); [lia|].
rewrite (Z.max_l kk (k + Z.of_nat w)) by lia. destruct (Z.ltb_spec kk (kk + l0)); [|lia].
replace (kk + l0 - kk) with l0 by lia. reflexivity.
Qed.
Lemma img_nov_eq : forall lo hi k w, img_nov lo hi k w = true ->
(if Z.ltb lo (Z.min k hi) then [KImg lo (Z.min k hi)] else []) ++
(if Z.ltb (Z.max lo (k + Z.of_nat w)) hi then [KImg (Z.max lo (k + Z.of_nat w)) hi] else []) = [KImg lo hi].
Proof.
intros lo hi k w H. unfold img_nov in H. destruct (Z.ltb_spec lo hi); [|discriminate].
destruct (Z.leb_spec hi k).
- rewrite (Z.min_r k hi) by lia. destruct (Z.ltb_spec lo hi); [|lia].
destruct (Z.ltb_spec (Z.max lo (k + Z.of_nat w)) hi); [lia|]. reflexivity.
- apply Z.leb_le in H. destruct (Z.ltb_spec lo (Z.min k hi)); [lia|].
rewrite (Z.max_l lo (k + Z.of_nat w)) by lia. destruct (Z.ltb_spec lo hi); [|lia]. reflexivity.
Qed.
Lemma fastkeep_rel : ltac2:(TCodec.tc2 tcn__FxCarry "Q<'RM'R<'R5'='QJ'QL'8'?'C'N%2211%411'G&VAr3r6r5r2%544321(E%83>21'T4&T7r9r8r7r4%58432<;1=:(RH(9(>%11J%33K61%511%F3=71p0?1phNI1pnBO1pRLQ11poNQ31poJQ51poLQ71po6Q91phFQ;1").
Proof.
intros bc sp wa w wv K same br2 H.
destruct K as [[kb kk] w' v|[kb kk] len|[kb kk] len bk|lo hi|e' m'|e' lo' hi'|[eb ek] en|c1 m1 c2 m2|[kb kk] len fc|[kb kk] len];
cbn [fastkeep] in H; try discriminate.
- destruct len as [l0| | | | | | |]; try discriminate. destruct same; [|discriminate].
unfold prune1pcK. cbv zeta. rewrite (ktrim_nov _ _ _ _ _ _ H). reflexivity.
- unfold prune1pcK. cbv zeta. destruct wa as [wb k]. cbn [a_base a_off] in *.
destruct wb as [z| | | | | | |]; try discriminate. destruct z; try discriminate.
rewrite (img_nov_eq _ _ _ _ H). reflexivity.
- destruct len as [l0| | | | | | |]; try discriminate. destruct same; [|discriminate].
unfold prune1pcK. cbv zeta. rewrite (ktrim_nov _ _ _ _ _ _ H). reflexivity.
- destruct len as [l0| | | | | | |]; try discriminate. destruct same; [|discriminate].
unfold prune1pcK. cbv zeta. rewrite (ktrim_nov _ _ _ _ _ _ H). reflexivity.
Qed.
Lemma ranges_apart_pcS_eq : forall bc sp b1 k1 z1 br2 b2 k2 n2, (forall z, n2 <> ELit z) ->
ranges_apart_pcS bc sp b1 k1 z1 br2 b2 k2 n2 (xhiB bc n2)
(match br2, xhiB bc n2 with Some (lo2, hi2), Some h2 => end_hiB bc b2 k2 n2 lo2 hi2 h2 | _, _ => None end)
= ranges_apart_pcB bc sp b1 k1 (ELit z1) br2 b2 k2 n2.
Proof.
intros bc sp b1 k1 z1 br2 b2 k2 n2 Hn.
assert (E : ranges_apart_pcB bc sp b1 k1 (ELit z1) br2 b2 k2 n2 =
if (match sp_rng sp, br2, sp_h1 sp, xhiB bc n2 with
| Some (lo1, hi1), Some (lo2, hi2), Some h1, Some h2 =>
if (Z.leb (hi1 + k1 + h1) (lo2 + k2) || Z.leb (hi2 + k2 + h2) (lo1 + k1))%bool then true
else if match end_hiB bc b1 k1 (ELit z1) lo1 hi1 h1 with Some e1 => Z.leb e1 (lo2 + k2) | None => false end then true
else match end_hiB bc b2 k2 n2 lo2 hi2 h2 with Some e2 => Z.leb e2 (lo1 + k1) | None => false end
| _, _, _, _ => false
end) then true
else if in_sides_xB bc (sp_Dx sp) b2 k2 n2 then true
else if negb (shares_var b1 b2) then false
else if lin_ge0B bc [(b2, k2)] [(b1, k1); (ELit z1, 0%Z)] then true
else lin_ge0B bc [(b1, k1)] [(b2, k2); (n2, 0%Z)]).
{ unfold ranges_apart_pcB. destruct n2 as [z| | | | | | |]; [exfalso; exact (Hn z eq_refl)| ..]; reflexivity. }
rewrite E. unfold ranges_apart_pcS. cbv [orb negb].
destruct (shares_var b1 b2);
(destruct (sp_rng sp) as [[lo1 hi1]|]; [|reflexivity]);
(destruct br2 as [[lo2 hi2]|]; [|destruct (sp_h1 sp); destruct (xhiB bc n2); reflexivity]);
(destruct (sp_h1 sp) as [h1|]; [|destruct (xhiB bc n2); reflexivity]);
(destruct (xhiB bc n2) as [h2|]; [|reflexivity]);
change (end_hiB bc b1 k1 (ELit z1) lo1 hi1 h1) with (@None Z);
(destruct (hi1 + k1 + h1 <=? lo2 + k2); [reflexivity|]);
(destruct (hi2 + k2 + h2 <=? lo1 + k1); reflexivity).
Qed.
Lemma BXOK_None : ltac2:(TCodec.tc2 tcn__FxCarry "8'RM&TLr1(5'UH%211%5241phF71").
Proof. intros bc x H. discriminate. Qed.
Lemma prune1pcKS_eq : ltac2:(TCodec.tc2 tcn__FxCarry "Q:'RM'R<'R5'='QJ'QL'8'?'C'N%2211%411'G'T4&YGr8r7r6r5r4r3r2r1&;%A1?&X?%13;64%43331&D%13553%@:?>=<;:9831&T7%18A@?>=<;:%E3D31phNG1pnBM1pRLO1poNQ11poJQ31poLQ51po6Q71phFQ91").
Proof.
intros bc sp wa w wv K same br2. unfold prune1pcKS.
rewrite (prune1pcKF_eq bc None None (BXOK_None bc) (BXOK_None bc)).
destruct same; [reflexivity|].
destruct K as [[kb kk] w' v|[kb kk] len|[kb kk] len bk|lo hi|e' m'|e' lo' hi'|[eb ek] en|c1 m1 c2 m2|[kb kk] len fc|[kb kk] len];
try reflexivity;
(destruct len as [l0| | | | | | |]; [reflexivity| ..]);
cbn [mk_pre fst snd]; unfold prune1pcK; cbv zeta; cbn [a_base a_off];
(rewrite ranges_apart_pcS_eq by discriminate);
(destruct (ranges_apart_pcB _ _ _ _ _ _ _ _ _); [reflexivity|]);
try reflexivity;
(destruct (kcutB _ _ _ _ _ _ _ _); reflexivity).
Qed.
Definition pk_rel (K : kentry) (r' r : pk_res) : Prop := r' = r \/ (r' = PKeep /\ r = PRepl [K]).
Definition PRE_OK (bc : bctx) (K : kentry) (br2 : option (Z * Z)) (pre : option (option Z * option Z)) : Prop :=
match pre with None => True | Some p => p = mk_pre bc K br2 end.
Lemma prune1pcKF2_rel : ltac2:(TCodec.tc2 tcn__FxCarry "QF'RM'?'UH%211'R<'R5'='QJ'QL'8'C'N%2211%<11%=13%5211%?11&TLr;r:%3221r<%5213&U<r=r6r4r3%544321&Y@r7&YDr>r9r8r5%5;4<?BA326;1:&T7%186DC548=3%:3931p0<1p0C1p0F1pn8K1phNO1pnBQ41pRLQ61poNQ81poJQ:1poLQ<1po6Q>1pk8Q@1pk6QA1phFQE1").
Proof.
intros bc i1 i2 sp wa w wv K same br2 pre H1 H2 HP. unfold prune1pcKF2.
destruct (fastkeep K wa w same) eqn:E.
- right. split; [reflexivity|]. apply fastkeep_rel. exact E.
- left. destruct pre as [[h2o e2o]|].
+ cbn [PRE_OK] in HP. rewrite (surjective_pairing (mk_pre bc K br2)) in HP. injection HP as -> ->. apply prune1pcKS_eq.
+ rewrite (prune1pcKF_eq bc i1 i2 H1 H2). reflexivity.
Qed.
Lemma g1cB_nobase : ltac2:(TCodec.tc2 tcn__FxCarry "Q='RM'T;'QL'8'?'C'N%2211%411'G'QJ%711&QKr3%211(5%116%83631'<%11A&S:r6r5r4%43321&T3&T7&TB%116&T>%118&TD%11:&TC%11<r2%:8?8642=G1%<2>1%M3C>1p0F1phNQ01pnBQ61pRLQ81po8Q:1phFQ<1").
Proof.
intros bc sx K same br2 HK. unfold g1cB, obrB. rewrite HK.
destruct K as [[kb kk] w' v|[kb kk] len|[kb kk] len bk|lo hi|e' m'|e' lo' hi'|[eb ek] en|c1 m1 c2 m2|[kb kk] len fc|[kb kk] len];
cbn [kbase] in HK; try discriminate; try reflexivity.
unfold prune1pcB, prune1pB, prune1pcK. cbv zeta. destruct (sx_a sx) as [wb k]. cbn [a_base a_off].
destruct wb as [z| | | | | | |];
try (destruct (Z.ltb (hi - lo) (2 ^ 64)); [destruct (ranges_apart_pB _ _ _ _ _ _ _ _); reflexivity|reflexivity]).
destruct z; try reflexivity;
(destruct (Z.ltb (hi - lo) (2 ^ 64)); [destruct (ranges_apart_pB _ _ _ _ _ _ _ _); reflexivity|reflexivity]).
Qed.
Lemma chain_slow_nobase : ltac2:(TCodec.tc2 tcn__FxCarry "Q:'RM'<'T;%211'QL'Q0'8p021'?'C'N%2211%411'G'QJ%711&QKr3%211(5%116%83631%E1B&S4r6r5(9r4(>%11I%43J31%83761&S2r2%26:97>A1%F3=41p0?1phNI1pnDO1pRLQ31po:Q51phFQ91").
Proof.
intros bc sxs K same_of br2 HK. induction sxs as [|sx rest IH]; [reflexivity|].
cbn [chain_slow chainK2 flat_map]. rewrite app_nil_r, (g1cB_nobase bc sx K (same_of (sx_bid sx)) br2 HK).
destruct (prune1pcK _ _ _ _ _ K _ br2); [exact IH|reflexivity].
Qed.
Lemma flat_map_ext_in : forall (A B : Type) (f g : A -> list B) l, (forall x, In x l -> f x = g x) -> flat_map f l = flat_map g l.
Proof. intros A B f g l H. induction l as [|x r IH]; [reflexivity|]. cbn. rewrite H by (left; reflexivity). rewrite IH by (intros; apply H; right; assumption). reflexivity. Qed.
Lemma prune1pcKF3_eq : ltac2:(TCodec.tc2 tcn__FxCarry "M'G'RM'?'UH%211'R<'R5'='QJ'QL'8'C'N%2211%<11'T4phN21pnB71pRL91poN;1poJ=1poL?1po6A1pk8C1pk6D1phFH1&YF&YC%L3321").
Proof.
fe. rename x into bc, x0 into i1, x1 into i2, x2 into sp, x3 into wa, x4 into w, x5 into wv, x6 into K, x7 into same, x8 into br2.
unfold prune1pcKF3, prune1pcKF, zfKF. cbv zeta.
destruct K as [[kb kk] w' v|[kb kk] len|[kb kk] len bk|lo hi|e' m'|e' lo' hi'|[eb ek] en|c1 m1 c2 m2|[kb kk] len fc|[kb kk] len];
try reflexivity.
Qed.
Lemma prune1pcKF2'_eq : ltac2:(TCodec.tc2 tcn__FxCarry "Q1'G'RM'?'UH%211'R<'R5'='QJ'QL'8'C'N%2211%<11%=13%5211%?11'T4pn821phN61pnB;1pRL=1poN?1poJA1poLC1po6E1pk8G1pk6H1phFL1&YE&YD%Q03321").
Proof. fe. unfold prune1pcKF2', prune1pcKF2. rewrite prune1pcKF3_eq. reflexivity. Qed.
Lemma prune1pcKX_eq : ltac2:(TCodec.tc2 tcn__FxCarry "QE'RM'R4'?'UH%211%411'T;'QL'8'C'N%2211%:11%;13%5211%=11'G'T4&YHr8&XNr7r6%3221r5r4r3r2r1%;7:654321&YD&[6&T?%11;%32=1&TB%11>&T>%11@&TD%11B&TC%11D%=;H9C7531BA@?%L3K?1pn8N1phNQ21pnBQ71pRLQ91pk8Q=1po8Q<1ph4Q>1phFQD1").
Proof.
intros bc X sx i2 K same br2 pre. unfold prune1pcKX. rewrite prune1pcKF2'_eq. cbn [si_sx si_bx si_ke mk_sxi]. cbv zeta beta.
destruct K as [[kb kk] w' v|[kb kk] len|[kb kk] len bk|lo hi|e' m'|e' lo' hi'|[eb ek] en|c1 m1 c2 m2|[kb kk] len fc|[kb kk] len];
try reflexivity.
- destruct same; [|reflexivity]. unfold prune1pcKF2. cbn [fastkeep].
destruct pre as [[h2o e2o]|]; unfold prune1pcKS, prune1pcKF; cbv zeta; reflexivity.
- destruct len as [l0| | | | | | |]; try reflexivity. destruct same; [|reflexivity].
unfold prune1pcKF2, nov2. cbn [fastkeep]. unfold nov. destruct (Z.ltb 0 l0), (Z.ltb l0 two64), (Z.leb (kk + l0) (a_off (sx_a sx))), (Z.leb (a_off (sx_a sx) + Z.of_nat (sx_w sx)) kk); reflexivity.
- unfold prune1pcKF2. cbn [fastkeep]. destruct (sx_a sx) as [wb k]. cbn [a_base a_off].
destruct wb as [z| | | | | | |]; try reflexivity. destruct z; try reflexivity.
unfold img_nov. destruct (Z.ltb lo hi), (Z.leb hi k), (Z.leb (k + Z.of_nat (sx_w sx)) lo); reflexivity.
- destruct len as [l0| | | | | | |]; try reflexivity. destruct same; [|reflexivity].
unfold prune1pcKF2, nov2. cbn [fastkeep]. unfold nov. destruct (Z.ltb 0 l0), (Z.ltb l0 two64), (Z.leb (kk + l0) (a_off (sx_a sx))), (Z.leb (a_off (sx_a sx) + Z.of_nat (sx_w sx)) kk); reflexivity.
- destruct len as [l0| | | | | | |]; try reflexivity. destruct same; [|reflexivity].
unfold prune1pcKF2, nov2. cbn [fastkeep]. unfold nov. destruct (Z.ltb 0 l0), (Z.ltb l0 two64), (Z.leb (kk + l0) (a_off (sx_a sx))), (Z.leb (a_off (sx_a sx) + Z.of_nat (sx_w sx)) kk); reflexivity.
Qed.
Lemma chainK2F2_eq : ltac2:(TCodec.tc2 tcn__FxCarry "R2'RM'R4'?'UH%211%411'<'T;%211'QL'QJ%911'Q0'8p021'C'N%2211%@11%A13%5211%C11&UAr9r8%3221&TLr:%2214'Gr6&QKr7%211%53G41&U<r<r5r4%443?21%Q21O&V1r=r;&M'ZI&XN%11;%44Q931E%88761JIAC<&S2%169HLKCE%G3<31p0>1p0D1p0K1p0O1pn8Q41phNQ81pnDQ=1pn0QA1pRLQD1po:QF1pQP2QK1ph4QK1phFR11").
Proof.
intros bc X xo sxs. induction sxs as [|sx rest IH]; intros K okb same_of br2 pre HX Hxo Hokb HP; [reflexivity|].
cbn [map chainK2F2 chainK2]. rewrite prune1pcKX_eq. cbn [si_sx si_bx mk_sxi].
destruct (prune1pcKF2_rel bc (xget X (sx_bid sx)) xo (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) K (same_of (sx_bid sx)) br2 pre (HX (sx_bid sx)) Hxo HP)
as [E|[E1 E2]].
- rewrite E. destruct (prune1pcK _ _ _ _ _ K _ br2) as [|l]; [apply IH; assumption|].
destruct okb as [kb|]; [|(rewrite chain_slowF_eq; reflexivity)].
apply flat_map_ext_in. intros K' _. destruct (kbase K') as [kb'|] eqn:HB; [|(rewrite chain_slowF_eq; reflexivity)].
destruct (expr_eqb kb' kb) eqn:EQ; [|(rewrite chain_slowF_eq; reflexivity)].
apply p_expr_eqb_eq in EQ. subst kb'. apply IH; [exact HX|exact Hxo|symmetry; exact HB|exact I].
- rewrite E1, E2. rewrite (IH K okb same_of br2 pre HX Hxo Hokb HP).
destruct okb as [kb|].
+ cbn [flat_map]. rewrite <- Hokb, p_expr_eqb_refl, app_nil_r. reflexivity.
+ symmetry. apply chain_slow_nobase. symmetry. exact Hokb.
Qed.
Lemma chainKFF2_eqG : ltac2:(TCodec.tc2 tcn__FxCarry "S6'RM'R4'?'UH%211%411'ZI'8pQP021'<'T;%211'QL'QJ%<11'Q0pQP019'C'N%2211%B11%C13%5211%E11&UAr:r9%3221&TLr;%2214'Gr6&QKr7%211%53F41&U<r=r8r5r4%544321&[>r1%23Q31@&XNr?r2%3221%<11(E%E3Q=21'T4&T7rA&TBr3%211&T>%113&TD%115&TC%117r<&T?%11:%Q;11%?8>;97541Q;(RG%Q83B21p0D1p0L1po8R01%R21QO&V3&X9&Mr>%Q211%34R7R;1QD%52A1%78Q4Q=1QJQIQ<QAQC&S2%16Q6QHQLQKQ>QC%QG3;31p0=1p0Q>1p0QE1p0QL1p0R01pn8R51phNR91pnDR>1pn0RA1pRLRD1po:RF1po0RJ1pQP2RO1ph4RO1phFS51").
Proof.
intros bc X xo skip sxs K okb same_of br2 pre HX Hxo Hokb HP. induction sxs as [|sx rest IH]; intros HS; [reflexivity|].
assert (IH' : chainKFF2 bc xo (mk_flG skip (map (mk_sxi X) rest)) K okb same_of br2 pre = chainK2 bc rest K okb same_of br2)
by (apply IH; intros sx' Hin; apply HS; right; exact Hin).
cbn [map mk_flG chainK2].
destruct (skip (mk_sxi X sx)) eqn:EV.
{ rewrite (HS sx (or_introl eq_refl) EV). exact IH'. }
cbn [chainKFF2]. rewrite prune1pcKX_eq. cbn [si_sx si_bx mk_sxi].
destruct (prune1pcKF2_rel bc (xget X (sx_bid sx)) xo (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) K (same_of (sx_bid sx)) br2 pre (HX (sx_bid sx)) Hxo HP)
as [E|[E1 E2]].
- rewrite E. destruct (prune1pcK _ _ _ _ _ K _ br2) as [|l]; [exact IH'|].
destruct okb as [kb|]; [|(rewrite chain_slowF_eq; reflexivity)].
apply flat_map_ext_in. intros K' _. destruct (kbase K') as [kb'|] eqn:HB; [|(rewrite chain_slowF_eq; reflexivity)].
destruct (expr_eqb kb' kb) eqn:EQ; [|(rewrite chain_slowF_eq; reflexivity)].
apply p_expr_eqb_eq in EQ. subst kb'. apply chainK2F2_eq; [exact HX|exact Hxo|symmetry; exact HB|exact I].
- rewrite E1, E2, IH'.
destruct okb as [kb|].
+ cbn [flat_map]. rewrite <- Hokb, p_expr_eqb_refl, app_nil_r. reflexivity.
+ symmetry. apply chain_slow_nobase. symmetry. exact Hokb.
Qed.
Fixpoint entC (bc : bctx) (sxs : list stx) (kn : list kentry) (infos : list (option einfo)) : list kentry :=
match kn, infos with
| K :: rest, oi :: irest =>
(match oi with
| Some ei => chainK2 bc sxs K (kbase K) (match kbase K with Some _ => Pos.eqb (ei_bid ei) | None => fun _ => false end)
(match kbase K with Some _ => ei_br ei | None => None end)
| None => chainK2 bc sxs K None (fun _ => false) None
end) ++ entC bc sxs rest irest
| _, _ => []
end.
Definition ei_strip (oi : option einfo) : option (positive * option (Z * Z)) :=
match oi with Some ei => Some (ei_bid ei, ei_br ei) | None => None end.
Lemma entC_strip : ltac2:(TCodec.tc2 tcn__FxCarry "Q8'RM'<'T;%211'QL%411'?'S7%211%811'G'C'Q0'N%3211%911%5241%;11%A11&M&V:r2%34>521r1%54@741%?3731&V=r6r5r4r3%544321%64543;%G3L21p091pkBJ1pk@K1pl8Q01po:Q31phFQ71").
Proof.
intros bc sxs kn. induction kn as [|K rest IH]; intros infos1 infos2 H; [reflexivity|].
destruct infos1 as [|o1 r1]; destruct infos2 as [|o2 r2]; cbn [map] in H; try discriminate; [reflexivity|].
injection H as H1 H2. cbn [entC]. rewrite (IH r1 r2 H2). f_equal.
destruct o1 as [e1|]; destruct o2 as [e2|]; cbn [ei_strip] in H1; try discriminate; [|reflexivity].
injection H1 as -> ->. reflexivity.
Qed.
Lemma entriesG_C : ltac2:(TCodec.tc2 tcn__FxCarry "Q>'RM'T1'<'T;%211&S@'QL%511'?'S7%211%911&RFr6r5%3221'L&RIr7%2216%43A16'[=&REr8%2216r4r3%65EA321'G&S8r9&SL%12C>%453?1C8&V=%145AE:%83M31p0:1p0B1p0H1pk>M1pl8Q21phLQ51po:Q71po<Q;1phFQ=1").
Proof.
intros bc t sxs bnds kn infos HT HS HF. induction HF as [|K oi rest irest HK HF IH]; [reflexivity|].
cbn [entriesG entC]. rewrite IH. f_equal.
destruct oi as [ei|]; [|reflexivity].
unfold mk_gl. rewrite pt_get_map.
destruct (pt_get bnds (ei_gid ei)) as [g|]; [|reflexivity].
destruct (inb g ei) eqn:Hinb; [|reflexivity].
apply chainKF_eq. intros sx Hsx Hv.
exact (verdict_keepG bc t sx g ei K HT (proj1 (Forall_forall _ _) HS sx Hsx) HK Hinb Hv).
Qed.
Definition EINFF (bc : bctx) (t : ntab) (K : kentry) (oi : option einfoF) : Prop :=
match oi with
| None => kdescr K = None
| Some e => EINF bc t K (Some (ef_ei e)) /\ (forall m, ef_m e = Some m -> ef_end e = ef_k e + m)
end.
Lemma obr_eqb_refl : ltac2:(TCodec.tc2 tcn__FxCarry "='?'C'N%2211%411'G'8&T2r1%2211(E%63521pmL81").
Proof. intros [[x y]|]; cbn [obr_eqb]; [rewrite !Z.eqb_refl|]; reflexivity. Qed.
Lemma nti_info : ltac2:(TCodec.tc2 tcn__FxCarry "Q:'RM'T1'QJ'Q0&RFr4r3%3221&[>'C%1287(Br2%24;:71&SO&RO%11:%32<1%:3851'G'?'RN%211&R3&T0r5%211%4361E(6(RD&RKr6%221K%42L1%62=1%@3=81p0B1p0N1pk:Q31ph>Q51po<Q71phFQ91").
Proof. intros bc t b id [HA _] H. exact (proj1 (proj2 (HA _ _ _ H))). Qed.
Lemma zlit64F_eq : ltac2:(TCodec.tc2 tcn__FxCarry "9'N'G&[;r1%211&RB%113%63731pQP681").
Proof.
intros z. unfold zlit64F, zlit64. rewrite zmod64_eq2.
destruct (Z.leb 0 z); [|reflexivity]. destruct (Z.ltb z two64); reflexivity.
Qed.
Lemma in_sides_num_in : ltac2:(TCodec.tc2 tcn__FxCarry "M'RM'<'C'R5'QJ%3221%511'N'G'8&W;r5r4r3r2r1%6554321(E%:3921&SBr6%251:987%>3=15p051pm8A1pkFB1ph>F1pRFE1phFL1").
Proof.
intros bc D b k n. induction D as [|[c m] r IH]; cbn [in_sides_num in_sidesB]; [discriminate|].
unfold num_sub, sub_itvB. cbv [andb].
intros H. destruct (if expr_eqb b (a_base c) then Z.leb (a_off c) k else false).
- destruct (match xloB bc m with Some ml => Z.leb (k + n) (a_off c + ml) | None => false end); [reflexivity|].
destruct (if if 0 <=? n then n <? two64 else false then xinsideB bc b k (ELit n) (a_base c) (a_off c) m else false); [reflexivity|exact (IH H)].
- destruct (if if 0 <=? n then n <? two64 else false then xinsideB bc b k (ELit n) (a_base c) (a_off c) m else false); [reflexivity|exact (IH H)].
Qed.
Lemma linV2_linV : ltac2:(TCodec.tc2 tcn__FxCarry "Q3'RM'ZI'Q0'?'C'N%2211%411'VN%611'G'8&WNr7r6r5r3r2r1%76654321(E%;3:21&WMr8r4%372<;:198%@3?16p061pjJC1pj4H1pj:I1pmNH1ph>N1pnLQ01phFQ21").
Proof.
intros bc si b obr glo ghi gx H. unfold linV2 in H. unfold linV.
destruct gx as [x|]; [|discriminate]. destruct (Pos.eqb b (sx_bid (si_sx si))); [discriminate|].
destruct (if Z.leb 0 (ghi - glo) then Z.ltb (ghi - glo) two63z else false) eqn:Eg; [|discriminate].
assert (Hz : zlit64 (ghi - glo) = ghi - glo).
{ unfold zlit64. rewrite two63z_val in Eg. destruct (Z.leb_spec 0 (ghi - glo)); [|discriminate].
destruct (Z.ltb_spec (ghi - glo) 9223372036854775808); [|discriminate].
destruct (Z.leb_spec 0 (ghi - glo)), (Z.ltb_spec (ghi - glo) two64); cbn [andb]; first [reflexivity | rewrite two64_val in *; lia]. }
unfold ranges_apart_pcF, elen. cbv zeta. rewrite Hz, <- zlit64F_eq.
destruct (match sp_rng (sx_sp (si_sx si)) with Some (lo1, hi1) => _ | None => false end); [reflexivity|].
destruct (in_sides_num bc (sp_D (sx_sp (si_sx si))) (gx_b x) glo (ghi - glo)) eqn:EN.
- destruct (lin_apartF _ _ _ _ _ _ _ _ _); [reflexivity|]. apply in_sides_num_in. exact EN.
- destruct (lin_apartF _ _ _ _ _ _ _ _ _); [reflexivity|]. exact H.
Qed.
Lemma z2i_val : ltac2:(TCodec.tc2 tcn__FxCarry "C'N&Q2'G'?%113&[9r2%211(6r1%2291%93741&Q8%117r3%=3?21p051pk4@1pQP6B1").
Proof.
intros z i H. destruct z as [|p|p]; cbn [z2i] in H; [injection H as <-; exact i0_val|exact (proj1 (P2Q.p2iQ4_val p i H))|discriminate].
Qed.
Lemma z2i_leb : ltac2:(TCodec.tc2 tcn__FxCarry "K'N&Q2'G'?%113&[9r4%211(6r2%2291%93741'8&Q3r3%2291&[Fr6r5%3221%B3851p0:1p0;1phHF1ph:G1ph>I1ph6J1").
Proof.
intros a b ai bi Ha Hb. apply z2i_val in Ha. apply z2i_val in Hb.
destruct (PrimInt63.leb ai bi) eqn:E; symmetry.
- apply Uint63Axioms.leb_spec in E. apply Z.leb_le. lia.
- apply Z.leb_gt. destruct (Z.le_gt_cases a b) as [H|H]; [|exact H].
exfalso. assert (X : PrimInt63.leb ai bi = true) by (apply Uint63Axioms.leb_spec; lia). congruence.
Qed.
Lemma rap_num : forall bc sp b1 k1 z1 br2 b2 k2 n2 lo1 hi1 h1 lo2 hi2 h2,
(forall z, n2 <> ELit z) -> sp_rng sp = Some (lo1, hi1) -> sp_h1 sp = Some h1 -> br2 = Some (lo2, hi2) -> xhiB bc n2 = Some h2 ->
(if Z.leb (hi1 + k1 + h1) (lo2 + k2) then true else if Z.leb (hi2 + k2 + h2) (lo1 + k1) then true
else match end_hiB bc b2 k2 n2 lo2 hi2 h2 with Some e2 => Z.leb e2 (lo1 + k1) | None => false end) = true ->
ranges_apart_pcB bc sp b1 k1 (ELit z1) br2 b2 k2 n2 = true.
Proof.
intros bc sp b1 k1 z1 br2 b2 k2 n2 lo1 hi1 h1 lo2 hi2 h2 Hn H1 H2 H3 H4 H. subst br2.
assert (E : ranges_apart_pcB bc sp b1 k1 (ELit z1) (Some (lo2, hi2)) b2 k2 n2 =
if (match sp_rng sp, Some (lo2, hi2), sp_h1 sp, xhiB bc n2 with
| Some (lo1, hi1), Some (lo2, hi2), Some h1, Some h2 =>
if (Z.leb (hi1 + k1 + h1) (lo2 + k2) || Z.leb (hi2 + k2 + h2) (lo1 + k1))%bool then true
else if match end_hiB bc b1 k1 (ELit z1) lo1 hi1 h1 with Some e1 => Z.leb e1 (lo2 + k2) | None => false end then true
else match end_hiB bc b2 k2 n2 lo2 hi2 h2 with Some e2 => Z.leb e2 (lo1 + k1) | None => false end
| _, _, _, _ => false
end) then true
else if in_sides_xB bc (sp_Dx sp) b2 k2 n2 then true
else if negb (shares_var b1 b2) then false
else if lin_ge0B bc [(b2, k2)] [(b1, k1); (ELit z1, 0%Z)] then true
else lin_ge0B bc [(b1, k1)] [(b2, k2); (n2, 0%Z)]).
{ unfold ranges_apart_pcB. destruct n2 as [z| | | | | | |]; [exfalso; exact (Hn z eq_refl)| ..]; reflexivity. }
rewrite E, H1, H2, H4. change (end_hiB bc b1 k1 (ELit z1) lo1 hi1 h1) with (@None Z). cbv [orb].
destruct (hi1 + k1 + h1 <=? lo2 + k2); [reflexivity|]. destruct (hi2 + k2 + h2 <=? lo1 + k1); [reflexivity|].
rewrite H. reflexivity.
Qed.
Lemma wlenF_eq : ltac2:(TCodec.tc2 tcn__FxCarry "<'='G'N&[0r1%211&[;&[K%114%311%93851poJ;1").
Proof. intros w. do 9 (destruct w as [|w]; [reflexivity|]). reflexivity. Qed.
Lemma kdescrF_eq : ltac2:(TCodec.tc2 tcn__FxCarry "A'QL'G'?'C'QJ'N%3221%512%5221%711&WKr1%211&SE%113%>3631pRL@1").
Proof.
intros K. unfold kdescrF, kdescr.
destruct K as [[kb kk] w' v|[kb kk] len|[kb kk] len bk|lo hi|e' m'|e' lo' hi'|[eb ek] en|c1 m1 c2 m2|[kb kk] len fc|[kb kk] len];
cbv zeta; rewrite ?wlenF_eq, ?two64_pow; try reflexivity; try (rewrite zlit64F_eq; reflexivity); destruct len; rewrite ?zlit64F_eq; reflexivity.
Qed.
Lemma scanF_sim : ltac2:(TCodec.tc2 tcn__FxCarry "R9'RM'<'QL%211'T1'S>'?'V;%211%811'S7%511%;11'G'C%126;%221;&Z5r;r:r9r8%544321(Br6r5%34AF21r4%54=G21%@3=71%@2BJ%A21J&T9r<%241@?=r3%=4HQ091r2%?48Q121%J3851'Fr7%M3Q61?'Q0'N%O211%Q811%Q1241%Q:11%Q@11&M&V:&@&V9%23Q?Q<1%54Q?Q<1Q2%64Q=851%74Q>96Q0%Q=3921%C2A1p0E1p0Q01pjHQI1poBQK1pkBQD1pjFQL1po@QN1pk@QJ1pjBQO1pj@R01po<R21pl8R41phFR81").
Proof.
intros bc kn. induction kn as [|K rest IH]; intros t gs gs' infos1 t1 gs1 infos2 t2 gs2 H1 H2.
- cbn in H1, H2. injection H1 as <- <- <-. injection H2 as <- <- <-. split; reflexivity.
- cbn [scanF scan_entries] in H1, H2. rewrite kdescrF_eq in H1.
destruct (kdescr K) as [[[kb kk] om]|].
+ destruct (intern bc t kb) as [[bid bi] t3].
lazymatch type of H2 with (let '(_, _) := ?X in _) = _ => destruct X as [gid' gs3'] end.
destruct (scan_entries bc rest t3 gs3') as [[i2 t5] g5] eqn:E2. injection H2 as <- <- <-.
destruct om as [m|].
* lazymatch type of H1 with (let '(_, _) := ?X in _) = _ => destruct X as [gid gs3] end.
destruct (scanF bc rest t3 _) as [[i1 t4] g4] eqn:E1. injection H1 as <- <- <-.
destruct (IH _ _ _ _ _ _ _ _ _ E1 E2) as [-> HI]. split; [reflexivity|]. cbn [map option_map ei_strip ef_ei ei_bid ei_br]. rewrite HI. reflexivity.
* destruct (scanF bc rest t3 gs) as [[i1 t4] g4] eqn:E1. injection H1 as <- <- <-.
destruct (IH _ _ _ _ _ _ _ _ _ E1 E2) as [-> HI]. split; [reflexivity|]. cbn [map option_map ei_strip ef_ei ei_bid ei_br]. rewrite HI. reflexivity.
+ destruct (scanF bc rest t gs) as [[i1 t4] g4] eqn:E1.
destruct (scan_entries bc rest t gs') as [[i2 t5] g5] eqn:E2.
injection H1 as <- <- <-. injection H2 as <- <- <-.
destruct (IH _ _ _ _ _ _ _ _ _ E1 E2) as [-> HI]. split; [reflexivity|]. cbn [map option_map ei_strip]. rewrite HI. reflexivity.
Qed.
Lemma scanF_okG : ltac2:(TCodec.tc2 tcn__FxCarry "QN'RM'<'QL%211'T1'S>'?'V;%211%811&RFr7r5%3221'G'C%127<%221<&Z5r8r6%342:19(Br4r3%34@E21r2%54;F21%>3;71'Fr9%E218'=%K11'QJ'Q0%E221&[>r1&SO%12:>%43531%32OB%637A1p031pn291pkF=1'[=&TM%12CJ%35Q@Q:1OQ6%F251%G2E1p0I1p0Q91pjBQB1po>QD1pk>Q@1pj@QE1po<QG1pl8QI1phFQM1").
Proof.
intros bc kn. induction kn as [|K rest IH]; intros t gs infos t' gs' HT H.
- cbn in H. injection H as <- <- <-. split; [exact HT|]. split; [intros; assumption|]. constructor.
- cbn [scanF] in H. rewrite kdescrF_eq in H.
destruct (kdescr K) as [[[kb kk] om]|] eqn:HD.
+ destruct (intern bc t kb) as [[bid bi] t1] eqn:EI.
destruct (intern_ok _ _ _ _ _ _ HT EI) as (HT1 & Hbi & HIn & Hm1).
assert (STEP : forall infos2 t2 gid ke, Forall2 (EINFF bc t2) rest infos2 -> (forall k p, In p (nt_bucket t1 k) -> In p (nt_bucket t2 k)) ->
(forall m, om = Some m -> ke = kk + m) ->
Forall2 (EINFF bc t2) (K :: rest) (Some (EF bid gid kb (bi_br bi) kk om ke) :: infos2)).
{ intros infos2 t2 gid ke HF Hm2 Hke. constructor; [|exact HF]. cbn [EINFF EINF ef_ei ei_kb ei_k ei_m ei_bid ei_br ef_end ef_k ef_m].
split; [|exact Hke]. split; [exact HD|]. split; [apply Hm2; exact HIn|]. rewrite Hbi. reflexivity. }
destruct om as [m|].
* lazymatch type of H with (let '(_, _) := ?X in _) = _ => destruct X as [gid gs0] end.
destruct (scanF bc rest t1 _) as [[infos2 t2] gs2] eqn:ES.
injection H as <- <- <-.
destruct (IH _ _ _ _ _ HT1 ES) as (HT2 & Hm2 & HF).
split; [exact HT2|]. split; [intros k p Hp; apply Hm2; apply Hm1; exact Hp|].
apply STEP; [exact HF|exact Hm2|intros m' E; injection E as <-; reflexivity].
* destruct (scanF bc rest t1 gs) as [[infos2 t2] gs2] eqn:ES.
injection H as <- <- <-.
destruct (IH _ _ _ _ _ HT1 ES) as (HT2 & Hm2 & HF).
split; [exact HT2|]. split; [intros k p Hp; apply Hm2; apply Hm1; exact Hp|].
apply STEP; [exact HF|exact Hm2|intros m' E; discriminate].
+ destruct (scanF bc rest t gs) as [[infos2 t2] gs2] eqn:ES.
injection H as <- <- <-.
destruct (IH _ _ _ _ _ HT ES) as (HT2 & Hm2 & HF).
split; [exact HT2|]. split; [exact Hm2|]. constructor; [exact HD | exact HF].
Qed.
Lemma stores_partF2_eq : ltac2:(TCodec.tc2 tcn__FxCarry "O'RM'R4'?'UH%211%411'<'T;%211&UAr3r2%3221'G'QL%911&ZEr4&M'ZI&XN%11;%44?31;%7261&T:%128>%=3;31p0?1po:D1ph4H1phFN1").
Proof.
intros bc X sxs HX. induction sxs as [|sx rest IH]; [reflexivity|].
cbn [map stores_partF2 stores_part si_sx si_bx mk_sxi]. rewrite IH.
rewrite (chainK2F2_eq bc X (xget X (sx_bid sx)) rest); [reflexivity|exact HX|apply HX| |exact I].
destruct (sx_a sx); reflexivity.
Qed.
Lemma mk_sctx_rng : ltac2:(TCodec.tc2 tcn__FxCarry "Q0'RM'UD'R5'='QJ'G'?'C'N%2211%411&R;&XCr5r4(QFr3r2r1%43321%83761%:11&RK&QG%118%32<1%E3@51poHG1poJI1ph6K1piLM1phFO1").
Proof.
intros bc ex a w v. unfold mk_sctx, mk_sprepF, elen.
destruct (Z.eqb (zlit64 (Z.of_nat w)) (Z.of_nat w)); [|reflexivity].
destruct (disj_both bc (be_kd ex) (a_base a) (a_off a) (Z.of_nat w)); reflexivity.
Qed.
Lemma mk_sctx_D : ltac2:(TCodec.tc2 tcn__FxCarry "Q6'RM'R5'='QJ'G'<'C%1264%311&R9&XCr4&X6%112(QFr3r2r1%43321%93861%;11&S5&RL%11<&QG%11:&QH%11<&RB&[K%11>%311%;5E9751%M3I=1poHO1poJQ11ph6Q31phFQ51").
Proof. intros bc a w v. unfold mk_sctx. rewrite mk_sprepF_eq. reflexivity. Qed.
Lemma mk_sctx_eq : ltac2:(TCodec.tc2 tcn__FxCarry "M'RM'R5'='QJ'G'R<&XCr4&X6%112(QFr3r2r1%43321%93861&SM&QG%117&QH%119&QI%11:%74@531%D3C91poHF1poJH1ph6J1phFL1").
Proof. intros bc a w v. unfold mk_sctx. apply mk_sprepF_eq. Qed.
Lemma mk_stxsC2_eq : ltac2:(TCodec.tc2 tcn__FxCarry "L'RM'<'R6%211'T1'G'C'T;%711%3215&XJr2&M'R<&XCr3&X6%112%4231%74A618r1%;3:21&SN%138<3%C3?31po<E1plLG1phFK1").
Proof.
intros bc log t. induction log as [|[a w v] older IH]; [reflexivity|].
cbn [map mk_stxsC2 mk_stxs]. rewrite IH, mk_sctx_rng, mk_sctx_eq. destruct (mk_stxs bc older t) as [sxs t1]. rewrite intern_r_eq. reflexivity.
Qed.
Definition LB (bc : bctx) (t : ntab) (lb : option (expr * positive * binfo)) : Prop :=
match lb with Some (b', id, bi) => In (b', id) (nt_bucket t (bkey b')) /\ bi = BI b' (base_rangeB bc b') | None => True end.
Definition LG (gs : gst) (lg : option (positive * positive * positive)) : Prop :=
match lg with Some (b, gk, gid) => exists inner, pt_get (gs_gid gs) b = Some inner /\ pt_get inner gk = Some gid | None => True end.
Lemma intern_c_eq : ltac2:(TCodec.tc2 tcn__FxCarry "Q0'RM'T1'?'C'QJ'Q0%3221'RN%5221%711&RFr4r3%3221&U3r5%23154'G%?2=;%@21B&W=r6%2417;:&SD%1339<%83631p0:1p0>1ph>H1plBD1po<M1phFO1").
Proof.
intros bc t lb b HT HL. destruct lb as [[[b' id] bi]|]; [|exact (internF_eq bc t b)]. cbn [intern_c]. rewrite internF_eq, BLKF.expr_eqbF_eq.
destruct (expr_eqb b b') eqn:E; [|reflexivity]. apply p_expr_eqb_eq in E. subst b'.
destruct HL as [HIn ->]. unfold intern.
destruct (alookupE (nt_bucket t (bkey b)) b) as [id0|] eqn:HL.
- pose proof (alookupE_Some _ _ _ HL) as H0. destruct HT as [HA HB].
rewrite (HB _ _ _ _ H0 HIn). rewrite (proj1 (proj2 (HA _ _ _ HIn))). reflexivity.
- exfalso. exact (alookupE_None _ _ id HL HIn).
Qed.
Lemma ggroup_c_eq : ltac2:(TCodec.tc2 tcn__FxCarry "I'S>'?'C'Q0%2211%3212%511&U4r4r3%3221'G%:29<&VGr5r2%342871&VF%13493%83731p0:1pj8B1phJC1plDA1pj@H1").
Proof.
intros gs lg bid gk HL. destruct lg as [[[b gk'] gid]|]; [|reflexivity]. cbn [ggroup_c].
destruct (Pos.eqb_spec bid b) as [->|]; [|reflexivity]. destruct (Pos.eqb_spec gk gk') as [->|]; [|reflexivity].
destruct HL as (inner & H1 & H2). unfold ggroupK. rewrite H1, H2. reflexivity.
Qed.
Lemma LB_mono : ltac2:(TCodec.tc2 tcn__FxCarry "Q4'RM'T1'?'C'QJ'Q0%3221'RN%5221%711'=%911&[>r1&SOr5r2%3221%63<51r3%6251%93?51p041pn2A1pkF=1&U3r4%23<1;r6%4313:p031p071plBG1po>Q01po<Q11phFQ31").
Proof. intros bc t t' [[[b' id] bi]|] Hm H; [|exact I]. destruct H as [H1 H2]. split; [apply Hm; exact H1|exact H2]. Qed.
Lemma ggroupK_LG : ltac2:(TCodec.tc2 tcn__FxCarry "M'S>'Q0'G'C%1234&VFr5r4r3%43321(Br2r1%34<=21%<3:51&U4(6%>2@@%?21A%94BB=<%:43C1<%5231%72;1p091pjDH1pj6H1pj8I1phJJ1pj@L1").
Proof.
intros gs bid gk gid gs0 H. unfold ggroupK in H.
destruct (pt_get (match pt_get (gs_gid gs) bid with Some i => i | None => PTLeaf end) gk) as [g|] eqn:E.
- injection H as <- <-. exists (match pt_get (gs_gid gs) bid with Some i => i | None => PTLeaf end). split; [|exact E].
destruct (pt_get (gs_gid gs) bid) as [i|] eqn:E2; [reflexivity|]. rewrite pt_get_leaf in E. discriminate.
- injection H as <- <-. cbn [gs_gid LG]. eexists. rewrite pt_gss. split; [reflexivity|]. apply pt_gss.
Qed.
Lemma bnd_addF_gid : ltac2:(TCodec.tc2 tcn__FxCarry "M'S>'Q0'?'C'N%2211%411'G'R4%118%211&S<&UGr6r5r4r3r2r1%76654321%911%:18%?3<21pjNC1plHD1pmNC1phJI1pj6J1pj@L1").
Proof.
intros. unfold bnd_addF. destruct (pt_get (gs_bnds gs) gid) as [[[b o] [l h]]|]; [|reflexivity].
destruct (Z.leb l lo); [destruct (Z.leb hi h)|]; reflexivity.
Qed.
Lemma scanF2_eq : ltac2:(TCodec.tc2 tcn__FxCarry "QB'RM'<'QL%211'T1'S>'?'C'QJ'Q0%3221'RN%5221%711%7255%8216%:11&RFr6r4%3221&U3r7r5r3%43321&U4%1243'G'V;%H11%N11%I21L%J21L&Z6r9r8%3621?C>B&Z5%1443AE%<3731p0>1p0A1p0G1plDL1plBQ01pj@Q91po<Q;1pl8Q=1phFQA1").
Proof.
intros bc kn. induction kn as [|K rest IH]; intros t gs lb lg HT HL HG; [reflexivity|].
cbn [scanF2 scanF]. destruct (kdescrF K) as [[[kb kk] om]|] eqn:HD.
- rewrite (intern_c_eq _ _ _ _ HT HL).
destruct (intern bc t kb) as [[bid bi] t1] eqn:EI.
destruct (intern_ok _ _ _ _ _ _ HT EI) as (HT1 & Hbi & HIn & Hm1).
assert (HL1 : LB bc t1 (Some (kb, bid, bi))) by (split; assumption).
destruct om as [m|].
+ rewrite (ggroup_c_eq _ _ _ _ HG). unfold ggroupF.
destruct (ggroupK gs bid (gkeyF kk)) as [gid gs0] eqn:EG.
rewrite (IH _ _ _ _ HT1 HL1); [reflexivity|]. cbn [LG]. rewrite bnd_addF_gid. exact (ggroupK_LG _ _ _ _ _ EG).
+ rewrite (IH _ _ _ _ HT1 HL1 HG). reflexivity.
- rewrite (IH _ _ _ _ HT HL HG). reflexivity.
Qed.
Definition nonov (si : sxi) (a e : PrimInt63.int) : bool :=
match si_iv si with Some (c, d) => if PrimInt63.leb e c then true else PrimInt63.leb d a | None => false end.
Fixpoint chainKI (bc : bctx) (xo : option bx) (fl : list (sxi * list sxi)) (a e : PrimInt63.int) (K : kentry) (okb : option expr)
(same_of : positive -> bool) (br2 : option (Z * Z)) : list kentry :=
match fl with
| [] => [K]
| (si, rest) :: fl' =>
if nonov si a e then chainKI bc xo fl' a e K okb same_of br2 else
match prune1pcKX bc si xo K (same_of (sx_bid (si_sx si))) br2 None with
| PKeep => chainKI bc xo fl' a e K okb same_of br2
| PRepl l =>
match okb with
| Some kb =>
flat_map (fun K' => match kbase K' with
| Some kb' => if expr_eqb kb' kb then chainK2F2 bc xo rest K' okb same_of br2 None else chain_slowF bc rest [K']
| None => chain_slowF bc rest [K']
end) l
| None => chain_slowF bc rest l
end
end
end.
Definition osame (b : positive) (si : sxi) : bool := if Pos.eqb b (sx_bid (si_sx si)) then false else true.
Lemma chainKFF2_eqG2 : ltac2:(TCodec.tc2 tcn__FxCarry "S6'RM'R4'?'UH%211%411'ZI'8pQP021'<'T;%211'QL'QJ%<11'Q0pQP019'C'N%2211%B11%C13%5211%E11&UAr:r9%3221&TLr;%2214'Gr6&QKr7%211%53F41&U<r=r8r5r4%544321&[>r1%23Q31@&XNr?r2%3221%<11(E%E3Q=21&Y@r<(RG&T7rA&TBr3%211&T>%113&TD%115&TC%117&T?%119%Q<11%>8=:864@1Q<%B3A@1p0D1p0L1po8R01%R21QO&V3&X9&Mr>%Q211%34R7R;1QD%52L1%78Q4Q=1QJQIQ<QAQC&S2%16Q6QHQLQKQ>QC%QG3;31p0=1p0Q>1p0QE1p0QL1p0R01pn8R51phNR91pnDR>1pn0RA1pRLRD1po:RF1po0RJ1pQP2RO1ph4RO1phFS51").
Proof.
intros bc X xo skip sxs K okb same_of br2 pre HX Hxo Hokb HP. induction sxs as [|sx rest IH]; intros HS; [reflexivity|].
assert (IH' : chainKFF2 bc xo (mk_flG skip (map (mk_sxi X) rest)) K okb same_of br2 pre = chainK2 bc rest K okb same_of br2)
by (apply IH; intros sx' Hin; apply HS; right; exact Hin).
cbn [map mk_flG chainK2].
destruct (skip (mk_sxi X sx)) eqn:EV.
{ destruct (HS sx (or_introl eq_refl) EV) as [E|[_ E2]].
- rewrite <- E. exact IH'.
- rewrite E2, IH'. destruct okb as [kb|].
+ cbn [flat_map]. rewrite <- Hokb, p_expr_eqb_refl, app_nil_r. reflexivity.
+ symmetry. apply chain_slow_nobase. symmetry. exact Hokb. }
cbn [chainKFF2]. rewrite prune1pcKX_eq. cbn [si_sx si_bx mk_sxi].
destruct (prune1pcKF2_rel bc (xget X (sx_bid sx)) xo (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) K (same_of (sx_bid sx)) br2 pre (HX (sx_bid sx)) Hxo HP)
as [E|[E1 E2]].
- rewrite E. destruct (prune1pcK _ _ _ _ _ K _ br2) as [|l]; [exact IH'|].
destruct okb as [kb|]; [|(rewrite chain_slowF_eq; reflexivity)].
apply flat_map_ext_in. intros K' _. destruct (kbase K') as [kb'|] eqn:HB; [|(rewrite chain_slowF_eq; reflexivity)].
destruct (expr_eqb kb' kb) eqn:EQ; [|(rewrite chain_slowF_eq; reflexivity)].
apply p_expr_eqb_eq in EQ. subst kb'. apply chainK2F2_eq; [exact HX|exact Hxo|symmetry; exact HB|exact I].
- rewrite E1, E2, IH'.
destruct okb as [kb|].
+ cbn [flat_map]. rewrite <- Hokb, p_expr_eqb_refl, app_nil_r. reflexivity.
+ symmetry. apply chain_slow_nobase. symmetry. exact Hokb.
Qed.
Lemma chainKI_eq : forall bc xo p sis a e K okb same_of br2,
chainKI bc xo (mk_flG p sis) a e K okb same_of br2
= chainKFF2 bc xo (mk_flG (fun si => if p si then true else nonov si a e) sis) K okb same_of br2 None.
Proof.
intros bc xo p sis a e K okb same_of br2. induction sis as [|si rest IH]; [reflexivity|].
cbn [mk_flG]. destruct (p si); [exact IH|]. cbn [chainKI]. destruct (nonov si a e); [exact IH|].
cbn [chainKFF2]. destruct (prune1pcKX bc si xo K (same_of (sx_bid (si_sx si))) br2 None); [exact IH|reflexivity].
Qed.
Lemma nonov_num : ltac2:(TCodec.tc2 tcn__FxCarry "Q@'R4'?'UH%211%411'T;&Q2'G'8&Y6&XNr4r3%3221r2r1%73321(E%;3:21'J&[E&Q8%118&[C&QH&T>%11?%311&[M+2+QK%3221%9251%=2;1&[K&TD%11I%311%?2;1%@218%C1L%E221%G291p0I1piHQ61ph6Q71po8Q91ph4Q;1").
Proof.
intros X sx a e H. unfold nonov in H. cbn [si_iv mk_sxi] in H.
destruct (iv_of (a_off (sx_a sx)) (Z.of_nat (sx_w sx))) as [[c d]|] eqn:E; [|discriminate].
apply iv_of_val in E. destruct E as (Ec & Ed & _).
destruct (PrimInt63.leb e c) eqn:E1.
- left. apply ileb_le in E1. lia.
- right. apply ileb_le in H. lia.
Qed.
Lemma nonov_keep : forall bc X sx K a e same br2,
ent_iv K = Some (a, e) -> nonov (mk_sxi X sx) a e = true ->
match kbase K with Some _ => same = true | None => a_base (sx_a sx) = ELit 0 end ->
pk_rel K PKeep (prune1pcK bc (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) K same br2).
Proof.
intros bc X sx K a e same br2 HI HN HS. apply nonov_num in HN.
destruct K as [[kb kk] w' v|[kb kk] len|[kb kk] len bk|lo hi|e' m'|e' lo' hi'|[eb ek] en|c1 m1 c2 m2|[kb kk] len fc|[kb kk] len];
cbn [ent_iv] in HI; try discriminate; cbn [kbase] in HS.
- subst same. apply iv_of_val in HI. destruct HI as (Ha & He & Hm). left. unfold prune1pcK. cbv zeta.
destruct (Z.leb_spec (kk + Z.of_nat w') (a_off (sx_a sx))); [reflexivity|].
destruct (Z.leb_spec (a_off (sx_a sx) + Z.of_nat (sx_w sx)) kk); [reflexivity|]. lia.
- destruct len as [l0| | | | | | |]; try discriminate. destruct l0 as [|p|p]; try discriminate.
subst same. apply iv_of_val in HI. destruct HI as (Ha & He & Hm). right. split; [reflexivity|].
unfold prune1pcK. cbv zeta. rewrite ktrim_nov; [reflexivity|]. unfold nov.
destruct (Z.ltb_spec 0 (Z.pos p)); [|lia]. destruct (Z.ltb_spec (Z.pos p) two64); [|rewrite two64_val in *; lia].
destruct (Z.leb_spec (kk + Z.pos p) (a_off (sx_a sx))); [reflexivity|]. apply Z.leb_le. lia.
- destruct len as [l0| | | | | | |]; try discriminate.
subst same. apply iv_of_val in HI. destruct HI as (Ha & He & Hm). left. unfold prune1pcK. cbv zeta.
rewrite (Z.mod_small l0 (2 ^ 64)) by lia.
destruct (Z.leb_spec (kk + l0) (a_off (sx_a sx))); [reflexivity|].
destruct (Z.leb_spec (a_off (sx_a sx) + Z.of_nat (sx_w sx)) kk); [reflexivity|]. lia.
- destruct (Z.ltb_spec lo hi) as [Hlh|]; [|discriminate].
destruct (z2b lo) as [a'|] eqn:Ea; [|discriminate]. destruct (z2b hi) as [e''|] eqn:Ee; [|discriminate].
injection HI as <- <-. apply z2b_val in Ea. apply z2b_val in Ee. right. split; [reflexivity|].
unfold prune1pcK. cbv zeta. rewrite HS. rewrite img_nov_eq; [reflexivity|]. unfold img_nov.
destruct (Z.ltb_spec lo hi); [|lia]. destruct (Z.leb_spec hi (a_off (sx_a sx))); [reflexivity|]. apply Z.leb_le. lia.
- destruct len as [l0| | | | | | |]; try discriminate. destruct l0 as [|p|p]; try discriminate.
subst same. apply iv_of_val in HI. destruct HI as (Ha & He & Hm). right. split; [reflexivity|].
unfold prune1pcK. cbv zeta. rewrite ktrim_nov; [reflexivity|]. unfold nov.
destruct (Z.ltb_spec 0 (Z.pos p)); [|lia]. destruct (Z.ltb_spec (Z.pos p) two64); [|rewrite two64_val in *; lia].
destruct (Z.leb_spec (kk + Z.pos p) (a_off (sx_a sx))); [reflexivity|]. apply Z.leb_le. lia.
- destruct len as [l0| | | | | | |]; try discriminate. destruct l0 as [|p|p]; try discriminate.
subst same. apply iv_of_val in HI. destruct HI as (Ha & He & Hm). right. split; [reflexivity|].
unfold prune1pcK. cbv zeta. rewrite ktrim_nov; [reflexivity|]. unfold nov.
destruct (Z.ltb_spec 0 (Z.pos p)); [|lia]. destruct (Z.ltb_spec (Z.pos p) two64); [|rewrite two64_val in *; lia].
destruct (Z.leb_spec (kk + Z.pos p) (a_off (sx_a sx))); [reflexivity|]. apply Z.leb_le. lia.
Qed.
Lemma mk_flG_nil : ltac2:(TCodec.tc2 tcn__FxCarry "L'ZI'8p021'<%114'G'C%1273%511&X9r2r1%3221(>%117%:3731&[>r3%23B71r5%11:(E%A3E21p051pnLH1p0:1pnNF1po0I1").
Proof.
intros skip sis. induction sis as [|x r IH]; intros H si Hin; [destruct Hin|].
cbn [mk_flG] in H. destruct (skip x) eqn:E; [|discriminate].
destruct Hin as [<-|Hin]; [exact E|exact (IH H si Hin)].
Qed.
Lemma mk_flG_ext : ltac2:(TCodec.tc2 tcn__FxCarry "M'ZI'8pQP021'<%114&[>r1r2%33821'Gr5%114r4%116%53=31p071pnL@1'C%12B>%@11&X9%129>r3%321@%?3531p091pnNF1po4I1po2J1").
Proof.
intros skip1 skip2 sis. induction sis as [|x r IH]; intros H; [reflexivity|].
cbn [mk_flG]. rewrite (H x (or_introl eq_refl)), IH by (intros; apply H; right; assumption). reflexivity.
Qed.
Lemma mk_flG_all : ltac2:(TCodec.tc2 tcn__FxCarry "L'ZI'8pQP021'<%114&[>r1r2%33821'Gr4%114(E%43<21p061pnL?1'C%12A=%?11&X9r3%221>(>%116%?3631p0:1pnNF1po0I1").
Proof.
intros skip sis. induction sis as [|x r IH]; intros H; [reflexivity|].
cbn [mk_flG]. rewrite (H x (or_introl eq_refl)). apply IH. intros; apply H; right; assumption.
Qed.
Local Notation int := PrimInt63.int.
Local Notation toZ := Uint63Axioms.to_Z.
Lemma z2l_bound : ltac2:(TCodec.tc2 tcn__FxCarry "O'N&Q2'G'?%113&[:r2%211(6r1%2291%93741'F&Q8%118r3%>3@21&[Ez%2214&[G&[M+2+QK%3221%52:1%>271%?2;1p0A1pl>L1pQP6N1").
Proof. exact z2l_val. Qed.
Lemma rng2l_val : ltac2:(TCodec.tc2 tcn__FxCarry "QI'?'C'N%2211%411&Q2'G%6222%811&YMr3%211(6(Br2r1%34;;21%52:1%<3:71'H'Fr6%94DD87%;2D1%B3D31&Q8r5%211%F3J1>r4%511%I3M1@&[Ez%221D&[G&[M+2+QK%3221%52J1%E271%:29K%82L4%H221%I241%J2?1%K2C1%L2H1qjNQ?1%O2Q@1qlHQA1%Q12QB1p0Q31ph>QA1ph6QB1pmLQD1").
Proof.
intros [[lo hi]|] a b H; [|discriminate]. cbn [rng2l] in H.
destruct (z2l lo) as [a'|] eqn:Ea; [|discriminate]. destruct (z2l hi) as [b'|] eqn:Eb; [|discriminate].
injection H as <- <-. apply z2l_val in Ea. apply z2l_val in Eb. exists lo, hi. intuition.
Qed.
Lemma mk_abj_val : ltac2:(TCodec.tc2 tcn__FxCarry "R1'?'C'N%2211%411&Q2'G%6222%811&X5r5&WAr4r3%3221%6251(6(Br2r1%34??21%52>1%@3>71'H'Fr8%94HH87%;2H1%F3H31&Q8%11D&[Cr7%22>1r6%4221&[M+2+QK%3221%9251%Q33Q7;1%=1N%<2I;%=215%Q73Q;31&[Ez%221>&[G%12@;%K231%L271%M2<1%N2J1qk0QE1%Q12QF1qlJQG1%Q32QH1p0Q51p6QG1p2QH1poJQL1pkFQM1pn>QL1").
Proof.
intros rng k w A B H. unfold mk_abj in H. destruct (iv_of k w) as [[c d]|] eqn:EI; [|discriminate].
destruct (rng2l rng) as [[lo1 hi1]|] eqn:ER; [|discriminate]. injection H as <- <-.
pose proof (iv_of_kb _ _ _ _ EI) as Hk. apply iv_of_val in EI. destruct EI as (Ec & Ed & Hw).
apply rng2l_val in ER. destruct ER as (lo & hi & -> & Elo & Ehi & Hlo & Hhi).
exists lo, hi. split; [reflexivity|]. rewrite !add_nov by lia. repeat split; lia.
Qed.
Definition gqj_of (gq : option (Z * Z)) : option (int * int) :=
match rng2l gq with Some (a, b) => Some (PrimInt63.add a B59, PrimInt63.add b B59) | None => None end.
Definition verdictJ (si : sxi) (b : positive) (gqj : option (int * int)) : bool :=
if Pos.eqb b (sx_bid (si_sx si)) then false else
match si_abj si, gqj with
| Some (A, B), Some (gl, gh) => if PrimInt63.leb A gl then true else PrimInt63.leb gh B
| _, _ => false
end.
Lemma zlit64_small : ltac2:(TCodec.tc2 tcn__FxCarry "D'N'F&[Ezr1%3221&[G&[M+2+QL%3221%5271%;271'G&RBr2%211%43A12p061pQP6C1").
Proof. intros z H. unfold zlit64. destruct (Z.leb_spec 0 z), (Z.ltb_spec z two64); cbn [andb]; try reflexivity; rewrite two64_val in *; lia. Qed.
Lemma verdictJ_F : ltac2:(TCodec.tc2 tcn__FxCarry "Q3'R4'?'UH%211%411'T;'Q0'C'N%2211%911'G'8&ZL&XNr4r3%3221r2&VMr1%211%93541(E%=3<21&ZKr5%=21<%331<:%B3A16p061pj<E1ph>J1po8L1ph4N1").
Proof.
intros X sx b gq H. unfold verdictJ in H. unfold verdictF. cbn [si_sx si_ab si_abj mk_sxi] in *.
destruct (Pos.eqb b (sx_bid sx)); [discriminate|].
destruct (mk_abj (sp_rng (sx_sp sx)) (iv_of (a_off (sx_a sx)) (Z.of_nat (sx_w sx)))) as [[A B]|] eqn:EA; [|discriminate].
apply mk_abj_val in EA. destruct EA as (lo1 & hi1 & -> & EA & EB & Hw).
unfold gqj_of in H. destruct (rng2l gq) as [[a b']|] eqn:EG; [|discriminate].
apply rng2l_val in EG. destruct EG as (GL & GH & -> & Ea & Eb & HGL & HGH).
unfold sx_m1. rewrite (zlit64_small (Z.of_nat (sx_w sx))) by lia.
assert (E1 : toZ (PrimInt63.add a B59) = GL + 2 ^ 59) by (rewrite add_nov by (rewrite B59_val; lia); rewrite B59_val; lia).
assert (E2 : toZ (PrimInt63.add b' B59) = GH + 2 ^ 59) by (rewrite add_nov by (rewrite B59_val; lia); rewrite B59_val; lia).
destruct (PrimInt63.leb A (PrimInt63.add a B59)) eqn:L1.
- apply ileb_le in L1. destruct (Z.leb_spec (hi1 + a_off (sx_a sx) + Z.of_nat (sx_w sx)) GL); [reflexivity|lia].
- apply ileb_le in H. destruct (Z.leb (hi1 + a_off (sx_a sx) + Z.of_nat (sx_w sx)) GL); [reflexivity|]. apply Z.leb_le. lia.
Qed.
Lemma ileb_gt : ltac2:(TCodec.tc2 tcn__FxCarry "B&Q2'G'8&Q3r2r1%3221(:%73621&[G&Q8%117r3%311%5231p071pQP4@1pQP0A1").
Proof.
intros x y H. destruct (Z.lt_ge_cases (toZ y) (toZ x)) as [L|L]; [exact L|].
exfalso. assert (X : PrimInt63.leb x y = true) by (apply Uint63Axioms.leb_spec; lia). congruence.
Qed.
Lemma ileb_true : ltac2:(TCodec.tc2 tcn__FxCarry "B&Q2&[E&Q8r2%211r1%411%6231'G'8&Q3r3%2219(E%63521p081pQP4@1pQP0A1").
Proof. intros x y H. apply Uint63Axioms.leb_spec. exact H. Qed.
Definition imax (x y : int) : int := if PrimInt63.leb x y then y else x.
Definition imin (x y : int) : int := if PrimInt63.leb x y then x else y.
Lemma imax_l : ltac2:(TCodec.tc2 tcn__FxCarry "<&Q2&[E&Q8r2%211&W6r1%2241%611%8251pQP4:1pQP0;1"). Proof. intros x y. unfold imax. destruct (PrimInt63.leb x y) eqn:E; [apply ileb_le in E; exact E|lia]. Qed.
Lemma imax_r : ltac2:(TCodec.tc2 tcn__FxCarry "<&Q2&[E&Q8r1%211&W6r2%2214%611%8251pQP4:1pQP0;1"). Proof. intros x y. unfold imax. destruct (PrimInt63.leb x y) eqn:E; [lia|apply ileb_gt in E; lia]. Qed.
Lemma imin_l : ltac2:(TCodec.tc2 tcn__FxCarry "<&Q2&[E&Q8&W7r2r1%3221%511%614%8221pQP4:1pQP0;1"). Proof. intros x y. unfold imin. destruct (PrimInt63.leb x y) eqn:E; [lia|apply ileb_gt in E; lia]. Qed.
Lemma imin_r : ltac2:(TCodec.tc2 tcn__FxCarry "<&Q2&[E&Q8&W7r2r1%3221%511%613%8221pQP4:1pQP0;1"). Proof. intros x y. unfold imin. destruct (PrimInt63.leb x y) eqn:E; [apply ileb_le in E; exact E|lia]. Qed.
Definition hull : Type := (int * int * int * int)%type.
Definition IMAXV : int := Uint63.of_Z (2 ^ 62).
Fixpoint hull_of (fl : list (sxi * list sxi)) : option hull :=
match fl with
| [] => Some (i0, IMAXV, IMAXV, i0)
| (si, _) :: r =>
match hull_of r with
| Some (A0, B0, c0, d0) =>
match si_abj si with
| Some (A, B) => match si_iv si with
| Some (c, d) => Some (imax A0 A, imin B0 B, imin c0 c, imax d0 d)
| None => None
end
| None => None
end
| None => None
end
end.
Lemma hull_of_cov : ltac2:(TCodec.tc2 tcn__FxCarry "RE'<'C'ZI%311%3221%511&Q2'G'?&VO%211&W0r5%211(6%>299%?21:%@21;(Br4r3%34??21r2%548A21r1%749C21%<291%D3A>1&[>%;4KJ75r8%33K21'H'F%J1C&Z:r7%211%H2GA%Q03521&Z;%115%H4Q4Q4DB%M2L1%Q53:31&[E&Q8%11Lr<%311%5231r;%611%71Q1%9221r:%:11%;1Q3%=221%=1Q3r9%?11%A231%N251%O2:1%Q02?1%Q12F1%Q22L1qiDQN1%Q52QO1qi4R01%Q72R11q6R21%Q92R31q2R41%Q;2R51p0Q=1pn<R:1pnLR<1p0QD1piFR:1pi8R;1p8R<1p4R=1pj0R?1").
Proof.
induction fl as [|[s0 r0] rest IH]; intros A0 B0 c0 d0 H si r Hin; [destruct Hin|].
cbn [hull_of] in H. destruct (hull_of rest) as [[[[A1 B1] c1] d1]|] eqn:ER; [|discriminate].
destruct (si_abj s0) as [[A B]|] eqn:EA; [|discriminate]. destruct (si_iv s0) as [[c d]|] eqn:EI; [|discriminate].
injection H as <- <- <- <-.
destruct Hin as [E|Hin].
- injection E as <- <-. exists A, B, c, d. split; [exact EA|]. split; [exact EI|].
pose proof (imax_r A1 A). pose proof (imin_r B1 B). pose proof (imin_r c1 c). pose proof (imax_r d1 d). lia.
- destruct (IH _ _ _ _ eq_refl si r Hin) as (A' & B' & c' & d' & H1 & H2 & H3 & H4 & H5 & H6).
exists A', B', c', d'. split; [exact H1|]. split; [exact H2|].
pose proof (imax_l A1 A). pose proof (imin_l B1 B). pose proof (imin_l c1 c). pose proof (imax_l d1 d). lia.
Qed.
Lemma mk_flG_in : ltac2:(TCodec.tc2 tcn__FxCarry "O'ZI'8pQP021'<%114&[>r1r2%33821'Gr4%114(:%43<21'H'C%12@<(B%14B>8<&X9r6r5%3221%B3751qn<D1%;2E1p0=1p0C1pnLL1pnNI1po0L1").
Proof.
intros skip sis si. induction sis as [|x rest IH]; intros Hin Hs; [destruct Hin|].
cbn [mk_flG]. destruct Hin as [<-|Hin].
- rewrite Hs. exists rest. left. reflexivity.
- destruct (IH Hin Hs) as [r Hr]. exists r. destruct (skip x); [exact Hr|right; exact Hr].
Qed.
Record sbe := SBE { sbe_b : positive; sbe_fl : list (sxi * list sxi); sbe_h : option hull }.
Fixpoint sb_find (l : list sbe) (b : positive) : option sbe :=
match l with [] => None | e :: r => if Pos.eqb b (sbe_b e) then Some e else sb_find r b end.
Fixpoint mk_sbl (all l : list sxi) (acc : list sbe) : list sbe :=
match l with
| [] => acc
| si :: r => let b := sx_bid (si_sx si) in
match sb_find acc b with
| Some _ => mk_sbl all r acc
| None => let fl := mk_flG (osame b) all in mk_sbl all r (SBE b fl (hull_of fl) :: acc)
end
end.
Definition SBE_OK (all : list sxi) (e : sbe) : Prop := sbe_h e = hull_of (mk_flG (osame (sbe_b e)) all).
Definition SBL_OK (all cur : list sxi) (l : list sbe) : Prop :=
forall e, In e l -> SBE_OK all e /\ sbe_fl e = mk_flG (osame (sbe_b e)) cur.
Lemma sb_find_in : ltac2:(TCodec.tc2 tcn__FxCarry "K'<'Z0%211'Q0'G'?%115&YNr3r2%3221(6r1%22<1%:3841'F&[>r4%23A91&Z1%11;%A3B1=%7241p091piHG1ph>F1pl>H1").
Proof.
induction l as [|x r IH]; intros b e H; [discriminate|]. cbn [sb_find] in H.
destruct (Pos.eqb_spec b (sbe_b x)) as [->|NE].
- injection H as <-. split; [left; reflexivity|reflexivity].
- destruct (IH b e H) as [H1 H2]. split; [right; exact H1|exact H2].
Qed.
Lemma sb_find_none : ltac2:(TCodec.tc2 tcn__FxCarry "K'<'Z0%211'Q0'G'?%115&YNr2r1%3221(5%11;%93731&[>r4%23?71&I&Z1%11;%@3A15%411p061piHF1p0;1ph>F1pl>H1").
Proof.
induction l as [|x r IH]; intros b H e Hin; [destruct Hin|]. cbn [sb_find] in H.
destruct (Pos.eqb b (sbe_b x)) eqn:EB; [discriminate|]. apply Pos.eqb_neq in EB.
destruct Hin as [<-|Hin]; [intros E; apply EB; symmetry; exact E|exact (IH b H e Hin)].
Qed.
Lemma mk_sbl_ok : ltac2:(TCodec.tc2 tcn__FxCarry "Q@'<'ZI%211'Z0%411&U=r3r1%33221'Fr4&XBr2%23371%93441&[>%13?96'Hr7r6r5%:3321%73C?1'G'Q0&Z1%11C&T?&Z<%11G%311%83751%G2:1qiHN1%A2O1p0C1pnLQ31%F3Q2NO%K3CBL%H3Q4K1p031piHQ61%Q1261%Q22M1p0Q41ph8Q91pl>Q<1ph<Q=1").
Proof.
intros all l. induction l as [|si r IH]; intros acc H; cbn [mk_sbl].
- split; [exact H|]. split; [intros si []|intros e He; exact He].
- destruct (sb_find acc (sx_bid (si_sx si))) as [e0|] eqn:EF.
+ destruct (IH acc H) as (H1 & H2 & H3). split; [exact H1|]. split; [|exact H3].
intros si' [<-|Hin]; [|exact (H2 si' Hin)].
destruct (sb_find_in _ _ _ EF) as [Hin0 Hb0]. exists e0. split; [apply H3; exact Hin0|exact Hb0].
+ set (e1 := SBE (sx_bid (si_sx si)) (mk_flG (osame (sx_bid (si_sx si))) all) (hull_of (mk_flG (osame (sx_bid (si_sx si))) all))).
assert (H' : SBL_OK all all (e1 :: acc)).
{ intros e [<-|Hin]; [split; reflexivity|exact (H e Hin)]. }
destruct (IH _ H') as (H1 & H2 & H3). split; [exact H1|]. split.
* intros si' [<-|Hin]; [|exact (H2 si' Hin)]. exists e1. split; [apply H3; left; reflexivity|reflexivity].
* intros e He. apply H3. right. exact He.
Qed.
Fixpoint forallbF {T : Type} (f : T -> bool) (l : list T) : bool :=
match l with [] => true | x :: r => if f x then forallbF f r else false end.
Lemma forallbF_in : forall T (f : T -> bool) l, forallbF f l = true -> forall x, In x l -> f x = true.
Proof.
intros T f l. induction l as [|y r IH]; intros H x Hin; [destruct Hin|]. cbn [forallbF] in H.
destruct (f y) eqn:E; [|discriminate]. destruct Hin as [<-|Hin]; [exact E|exact (IH H x Hin)].
Qed.
Definition hv_other (h : option hull) (gqj : option (int * int)) : bool :=
match h, gqj with
| Some (A0, B0, _, _), Some (gl, gh) => if PrimInt63.leb A0 gl then true else PrimInt63.leb gh B0
| _, _ => false
end.
Definition hv_same (h : option hull) (giv : option (int * int)) : bool :=
match h, giv with
| Some (_, _, c0, d0), Some (gl, gh) => if PrimInt63.leb gh c0 then true else PrimInt63.leb d0 gl
| _, _ => false
end.
Definition skipv5 (bc : bctx) (b : positive) (glo ghi : Z) (gx : option gxi) (gqj : option (int * int)) (si : sxi) : bool :=
if verdictJ si b gqj then true else linV2 bc si b glo ghi gx.
Definition skipo5 (bc : bctx) (b : positive) (glo ghi : Z) (gx : option gxi) (gqj : option (int * int)) (si : sxi) : bool :=
if Pos.eqb b (sx_bid (si_sx si)) then true else skipv5 bc b glo ghi gx gqj si.
Definition smemo : Type := list (saddr * expr * bool).
Fixpoint sm_find (m : smemo) (c : saddr) (e : expr) : option bool :=
match m with
| [] => None
| (c', e', r) :: rest =>
if (if expr_eqbF (a_base c) (a_base c') then if Z.eqb (a_off c) (a_off c') then expr_eqbF e e' else false else false) then Some r
else sm_find rest c e
end.
Fixpoint in_sidesM (bc : bctx) (m : smemo) (D : list (saddr * expr)) (b : expr) (k n : Z) : bool * smemo :=
match D with
| [] => (false, m)
| (c, e) :: r =>
match sm_find m c e with
| Some true => (true, m)
| Some false => in_sidesM bc m r b k n
| None => if sub_itvB bc b k n c e then (true, (c, e, true) :: m) else in_sidesM bc ((c, e, false) :: m) r b k n
end
end.
Definition linV2M (bc : bctx) (si : sxi) (b : positive) (glo ghi : Z) (gx : option gxi) (m : smemo) : bool * smemo :=
match gx with
| Some x =>
if Pos.eqb b (sx_bid (si_sx si)) then (false, m) else
if (if Z.leb 0 (ghi - glo) then Z.ltb (ghi - glo) two63z else false) then
let sx := si_sx si in
if in_sides_num bc (sp_D (sx_sp sx)) (gx_b x) glo (ghi - glo) then (true, m)
else if lin_apartF bc (si_bx si) (gx_bx x) (a_base (sx_a sx)) (a_off (sx_a sx)) (zlit64F (Z.of_nat (sx_w sx))) (gx_b x) glo (ghi - glo) then (true, m)
else in_sidesM bc m (sp_D (sx_sp sx)) (gx_b x) glo (ghi - glo)
else (false, m)
| None => (false, m)
end.
Fixpoint mk_flM (bc : bctx) (b : positive) (glo ghi : Z) (gx : option gxi) (gqj : option (int * int)) (same_skip : bool) (m : smemo)
(sis : list sxi) : list (sxi * list sxi) :=
match sis with
| [] => []
| si :: srest =>
if Pos.eqb b (sx_bid (si_sx si)) then
(if same_skip then mk_flM bc b glo ghi gx gqj same_skip m srest else (si, srest) :: mk_flM bc b glo ghi gx gqj same_skip m srest)
else if verdictJ si b gqj then mk_flM bc b glo ghi gx gqj same_skip m srest
else let '(v, m') := linV2M bc si b glo ghi gx m in
if v then mk_flM bc b glo ghi gx gqj same_skip m' srest else (si, srest) :: mk_flM bc b glo ghi gx gqj same_skip m' srest
end.
Definition MEMO_OK (bc : bctx) (b : expr) (k n : Z) (m : smemo) : Prop := forall c e r, In (c, e, r) m -> r = sub_itvB bc b k n c e.
Lemma sm_find_ok : ltac2:(TCodec.tc2 tcn__FxCarry "Q6'RM'QJ'N&ZA'R5'8&U5r8r7r6r5r4%6554321'G'?%11:&Z@r3%23871(6r2%22@1%93741&T<r:r9%3621CB@?%>3F:1p061p0A1pn<I1piHN1pi4L1plNN1pm8Q01pkFQ11ph>Q31phFQ51").
Proof.
intros bc b k n m c e r. induction m as [|[[c' e'] r'] rest IH]; intros H HF; [discriminate|]. cbn [sm_find] in HF. eF.
destruct (if expr_eqb (a_base c) (a_base c') then if Z.eqb (a_off c) (a_off c') then expr_eqb e e' else false else false) eqn:E.
- injection HF as <-. destruct (expr_eqb (a_base c) (a_base c')) eqn:E1; [|discriminate]. destruct (Z.eqb_spec (a_off c) (a_off c')) as [E2|]; [|discriminate].
apply p_expr_eqb_eq in E1. apply p_expr_eqb_eq in E. subst e'. destruct c as [cb co], c' as [cb' co']. cbn [a_base a_off] in *. subst cb' co'.
apply H. left. reflexivity.
- apply IH; [intros c0 e0 r0 H0; apply H; right; exact H0|exact HF].
Qed.
Lemma in_sidesM_ok : ltac2:(TCodec.tc2 tcn__FxCarry "Q7'RM'<'C'R5'QJ%3221%511'N&ZA&U5r6r4r3r2r1%6554321'F'G'8&;&W9r7r5%362:=1<;%536@1&SB%155@4?>%:3931&D%13;E6%E598CB1%?241p0A1plNI1pm8K1pkFL1ph>Q01pRFO1phFQ61").
Proof.
intros bc D b k n. induction D as [|[c e] r IH]; intros m H; [split; [reflexivity|exact H]|].
cbn [in_sidesM in_sidesB]. destruct (sm_find m c e) as [[|]|] eqn:EF.
- rewrite <- (sm_find_ok bc b k n m c e true H EF). split; [reflexivity|exact H].
- rewrite <- (sm_find_ok bc b k n m c e false H EF). exact (IH m H).
- destruct (sub_itvB bc b k n c e) eqn:ES.
+ split; [reflexivity|]. intros c0 e0 r0 [E|H0]; [injection E as <- <- <-; symmetry; exact ES|exact (H c0 e0 r0 H0)].
+ apply IH. intros c0 e0 r0 [E|H0]; [injection E as <- <- <-; symmetry; exact ES|exact (H c0 e0 r0 H0)].
Qed.
Definition GMEMO (bc : bctx) (glo ghi : Z) (gx : option gxi) (m : smemo) : Prop :=
match gx with Some x => MEMO_OK bc (gx_b x) glo (ghi - glo) m | None => True end.
Lemma linV2M_ok : ltac2:(TCodec.tc2 tcn__FxCarry "Q8'RM'ZI'Q0'N'?'VN%211&ZA&TNr7r4r3r2r1%6554321'F'G'8&;&WOr8r6r5%473>21=<;%637A1&WN%166A54@?%;3:31&D%13<F6%F5:8DC1%@241p0B1plNJ1pjJL1pj4Q01pj:Q11ph>Q31pnLQ51phFQ71").
Proof.
intros bc si b glo ghi gx m H. unfold linV2M, linV2. destruct gx as [x|]; [|split; [reflexivity|exact H]]. cbn [GMEMO] in *.
destruct (Pos.eqb b (sx_bid (si_sx si))); [split; [reflexivity|exact H]|].
destruct (if Z.leb 0 (ghi - glo) then Z.ltb (ghi - glo) two63z else false); [|split; [reflexivity|exact H]]. cbv zeta.
destruct (in_sides_num bc (sp_D (sx_sp (si_sx si))) (gx_b x) glo (ghi - glo)); [split; [reflexivity|exact H]|].
destruct (lin_apartF _ _ _ _ _ _ _ _ _); [split; [reflexivity|exact H]|].
exact (in_sidesM_ok bc _ _ _ _ m H).
Qed.
Lemma mk_flM_eq : ltac2:(TCodec.tc2 tcn__FxCarry "QE'RM'Q0'N'?'VN%211'C&Q2%2211%611'<'ZI%211&ZA&TNr8r6r5r4r1%6554321'F'G%A2<;%>11&X:r9r7(Er2r3%695@4?>=321&X9&Z>%168C7BA@%3215%>3<51(:%=9<G;FED198&Z?%16>I=HGF%921;%D3B41%F271p0H1plNQ01pnNQ21pj>Q61pjJQ;1pj4Q?1pj:Q@1ph>QB1phFQD1").
Proof.
intros bc b glo ghi gx gqj sis. induction sis as [|si rest IH]; intros m H; [split; reflexivity|].
cbn [mk_flM mk_flG]. unfold skipo5 at 1, skipv5 at 1 2.
destruct (Pos.eqb b (sx_bid (si_sx si))) eqn:EB.
- destruct (IH m H) as [I1 I2]. split; [exact I1|].
assert (EV : verdictJ si b gqj = false) by (unfold verdictJ; rewrite EB; reflexivity).
assert (EL : linV2 bc si b glo ghi gx = false) by (unfold linV2; destruct gx; [rewrite EB|]; reflexivity).
rewrite EV, EL, I2. reflexivity.
- destruct (verdictJ si b gqj); [exact (IH m H)|].
destruct (linV2M_ok bc si b glo ghi gx m H) as [E1 E2].
destruct (linV2M bc si b glo ghi gx m) as [v m']. cbn [fst snd] in E1, E2. rewrite <- E1.
destruct (IH m' E2) as [I1 I2]. destruct v; [split; assumption|]. rewrite I1, I2. split; reflexivity.
Qed.
Definition enj_of (K : kentry) (br2 : option (Z * Z)) (h2o e2o : option Z) : option (int * int * option int) :=
match eni_of2 K br2 h2o e2o with
| Some (el, eh, e2) => Some (PrimInt63.add el B59, PrimInt63.add eh B59, match e2 with Some x => Some (PrimInt63.add x B59) | None => None end)
| None => None
end.
Definition symnumJ (si : sxi) (enj : option (int * int * option int)) : bool :=
match si_a2j si, enj with
| Some (A, B), Some (el, eh, e2) =>
if PrimInt63.leb A el then true else if PrimInt63.leb eh B then true else
match e2 with Some e => PrimInt63.leb e B | None => false end
| _, _ => false
end.
Lemma ent_iv_descr : ltac2:(TCodec.tc2 tcn__FxCarry "QH'QL&Q2'QJ'N'G'?'C%1266%311&V>r6%211(6(Br5r4%34??21%52:1%>3:71%=2A@%?1A%?221%A11&SEr7%211r3%>4IH<1r2%A2J1%A4;:31%C2:1%L3:71'F&Q8%11;&[C&[M+2+QK%3221%52J1%Q63Q771%91Q1%82MB%9215%Q:3Q;31%>251p0@1p0O1plNQ?1pl4Q@1pl0QB1piHQD1ph6QE1pRLQG1").
Proof.
intros K a e kb kk m HI HD.
destruct K as [[b k] w' v|[b k] len|[b k] len bk|lo hi|e' m'|e' lo' hi'|[b k] n|a1 n1 a2 n2|[b k] len fc|[b k] len];
cbn [ent_iv kdescr] in *; try discriminate.
- injection HD as <- <- <-. apply iv_of_val in HI. destruct HI as (Ha & He & Hm). rewrite (zlit64_small _) by lia. split; assumption.
- destruct len as [l0| | | | | | |]; try discriminate. destruct l0 as [|p|p]; try discriminate.
injection HD as <- <- <-. apply iv_of_val in HI. destruct HI as (Ha & He & Hm). rewrite (zlit64_small _) by lia. split; assumption.
- destruct len as [l0| | | | | | |]; try discriminate.
injection HD as <- <- <-. apply iv_of_val in HI. destruct HI as (Ha & He & Hm). rewrite (zlit64_small _) by lia. split; assumption.
- destruct (Z.ltb_spec lo hi) as [Hlh|]; [|discriminate].
destruct (z2b lo) as [a'|] eqn:Ea; [|discriminate]. destruct (z2b hi) as [e''|] eqn:Ee; [|discriminate].
injection HI as <- <-. apply z2b_val in Ea. apply z2b_val in Ee.
destruct (Z.ltb_spec (hi - lo) (2 ^ 64)); [|lia]. injection HD as <- <- <-.
rewrite (zlit64_small (hi - lo)) by lia. split; lia.
- destruct len as [l0| | | | | | |]; try discriminate. destruct l0 as [|p|p]; try discriminate.
injection HD as <- <- <-. apply iv_of_val in HI. destruct HI as (Ha & He & Hm). rewrite (zlit64_small _) by lia. split; assumption.
- destruct len as [l0| | | | | | |]; try discriminate. destruct l0 as [|p|p]; try discriminate.
injection HD as <- <- <-. apply iv_of_val in HI. destruct HI as (Ha & He & Hm). rewrite (zlit64_small _) by lia. split; assumption.
Qed.
Lemma nonov_hull : forall X sx a e gl gh c0 d0 A B c d,
si_iv (mk_sxi X sx) = Some (c, d) -> si_abj (mk_sxi X sx) = Some (A, B) ->
toZ c0 <= toZ c -> toZ d <= toZ d0 ->
PrimInt63.leb gl a = true -> PrimInt63.leb e gh = true ->
(if PrimInt63.leb gh c0 then true else PrimInt63.leb d0 gl) = true ->
nonov (mk_sxi X sx) a e = true.
Proof.
intros X sx a e gl gh c0 d0 A B c d HI _ Hc Hd H1 H2 H3. unfold nonov. rewrite HI.
apply ileb_le in H1. apply ileb_le in H2.
destruct (PrimInt63.leb gh c0) eqn:E.
- apply ileb_le in E. rewrite (ileb_true e c) by lia. reflexivity.
- apply ileb_le in H3. destruct (PrimInt63.leb e c); [reflexivity|]. apply ileb_true. lia.
Qed.
Lemma p2iS_bound : ltac2:(TCodec.tc2 tcn__FxCarry "Q3'Q0&Q2'F&[Ez&Q8r3%211%5241&[Gr2%611%3251%;251'G'?%11?&Y?r5r4%3321>(6%12E<%93731&[M+2+QN%3221%C2E1p061p0A1pn<N1pn:O1ph8Q01pn2Q21").
Proof.
induction p as [q IH|q IH|]; intros acc pw r Ha H; cbn [p2iS] in H;
(destruct (PrimInt63.ltb m61 pw) eqn:El; [discriminate|]);
(assert (Q : toZ pw <= 2 ^ 61) by (rewrite <- m61_val; destruct (Z.le_gt_cases (toZ pw) (toZ m61)) as [Y|Y]; [exact Y|];
apply Uint63Axioms.ltb_spec in Y; congruence));
(assert (E2 : toZ (PrimInt63.add pw pw) = toZ pw + toZ pw) by (apply add_nov; lia)).
- assert (E1 : toZ (PrimInt63.add acc pw) = toZ acc + toZ pw) by (apply add_nov; lia).
apply IH in H; [exact H|rewrite E1, E2; lia].
- apply IH in H; [exact H|rewrite E2; lia].
- injection H as <-. rewrite add_nov by lia. lia.
Qed.
Lemma z2i_bound : ltac2:(TCodec.tc2 tcn__FxCarry "O'N&Q2'G'?%113&[9r2%211(6r1%2291%93741'F&Q8%118r3%>3@21&[Ez%2214&[G&[M+2+QN%3221%52:1%>271%?2;1p0A1pk4L1pQP6N1").
Proof.
intros z i H. pose proof (z2i_val z i H) as V. split; [exact V|].
destruct z as [|p|p]; cbn [z2i] in H; [lia| |discriminate].
pose proof (proj2 (P2Q.p2iQ4_val p i H)). lia.
Qed.
Lemma jleb : ltac2:(TCodec.tc2 tcn__FxCarry "M&Q2'N'G&Q8r4%211&[Cr2&[M+2+QK%3221%6251%;3<81'8&Q3r6r5%3221&[Fr3%22A1%D3841p0:1p0;1ph>H1ph6I1pQP4K1pQP0L1").
Proof.
intros x y a b Hx Hy. destruct (PrimInt63.leb x y) eqn:E; symmetry.
- apply ileb_le in E. apply Z.leb_le. lia.
- apply ileb_gt in E. apply Z.leb_gt. lia.
Qed.
Lemma addB_val : ltac2:(TCodec.tc2 tcn__FxCarry "L'N&Q2'G'?%113&[9r2%211(6r1%2291%93741&Q8&Q1&TJ%2291%411&[Cr3&[M+2+QK%3221%6251%F3H81p0>1pk4I1pQP6K1").
Proof. intros z i H. apply z2i_bound in H. destruct H as [V B]. rewrite add_nov by (rewrite B59_val; lia). rewrite B59_val. lia. Qed.
Lemma symnumJ_keep : ltac2:(TCodec.tc2 tcn__FxCarry "QG'RM'R4'?'UH%211%411'T;'QL'C'N%2211%911'G'8&ZJ&XNr4r3%3221&V<r2r1&;%E1>&X?r5%23165%53441&D%13663%;4:931%A2=1(E%E3D21'T4&T7r6&TB%11F&T>%11H&TD%11J&TC%11L(:%;8:8642M1J(RG%Q43>21p0@1phNQ71pRLQ<1po8Q>1ph4Q@1phFQF1").
Proof.
intros bc X sx K br2 H. unfold symnumJ in H. cbn [si_a2j mk_sxi] in H.
destruct (sp_h1 (sx_sp sx)) as [h1|] eqn:E2; [|discriminate].
destruct (Z.eqb_spec h1 (Z.of_nat (sx_w sx))) as [Eh1|]; [|discriminate].
destruct (mk_abj (sp_rng (sx_sp sx)) (iv_of (a_off (sx_a sx)) (Z.of_nat (sx_w sx)))) as [[A B]|] eqn:EA; [|discriminate].
apply mk_abj_val in EA. destruct EA as (lo1 & hi1 & E1 & EA & EB & Hw).
assert (EA' : toZ A = (hi1 + a_off (sx_a sx) + h1) + 2 ^ 59) by lia.
assert (EB' : toZ B = (lo1 + a_off (sx_a sx)) + 2 ^ 59) by lia.
assert (GEN : forall kb kk len lo2 hi2 h2, (forall z, len <> ELit z) -> xhiB bc len = Some h2 ->
match (match (match z2i (lo2 + kk), z2i (hi2 + kk + h2) with
| Some el, Some eh => match end_hiB bc kb kk len lo2 hi2 h2 with
| None => Some (el, eh, None)
| Some e2 => match z2i e2 with Some i => Some (el, eh, Some i) | None => None end end
| _, _ => None end) with
| Some (el, eh, e2) => Some (PrimInt63.add el B59, PrimInt63.add eh B59, match e2 with Some x => Some (PrimInt63.add x B59) | None => None end)
| None => None end) with
| Some (el, eh, e2i) => if PrimInt63.leb A el then true else if PrimInt63.leb eh B then true else
match e2i with Some e => PrimInt63.leb e B | None => false end
| None => false end = true ->
ranges_apart_pcB bc (sx_sp sx) (a_base (sx_a sx)) (a_off (sx_a sx)) (elen (sx_w sx)) (Some (lo2, hi2)) kb kk len = true).
{ intros kb kk len lo2 hi2 h2 Hn Eh HH.
destruct (z2i (lo2 + kk)) as [el|] eqn:Eel; [|discriminate]. destruct (z2i (hi2 + kk + h2)) as [eh|] eqn:Eeh; [|discriminate].
apply (rap_num bc _ _ _ _ _ _ _ _ lo1 hi1 h1 lo2 hi2 h2 Hn E1 E2 eq_refl Eh).
destruct (end_hiB bc kb kk len lo2 hi2 h2) as [e2|].
- destruct (z2i e2) as [ei|] eqn:Ee; [|discriminate]. cbv iota beta in HH.
rewrite (jleb _ _ _ _ EA' (addB_val _ _ Eel)), (jleb _ _ _ _ (addB_val _ _ Eeh) EB'), (jleb _ _ _ _ (addB_val _ _ Ee) EB') in HH. exact HH.
- cbv iota beta in HH. rewrite (jleb _ _ _ _ EA' (addB_val _ _ Eel)), (jleb _ _ _ _ (addB_val _ _ Eeh) EB') in HH. exact HH. }
destruct K as [[kb kk] w' v|[kb kk] len|[kb kk] len bk|lo hi|e' m'|e' lo' hi'|[eb ek] en|c1 m1 c2 m2|[kb kk] len fc|[kb kk] len];
try (cbv [enj_of eni_of2 fst snd mk_pre] in H; cbv iota beta in H; discriminate);
(destruct len as [z| | | | | | |]; [cbv [enj_of eni_of2 fst snd mk_pre] in H; cbv iota beta in H; discriminate| ..]);
cbv [enj_of eni_of2 fst snd mk_pre] in H; cbv iota beta zeta in H;
(destruct br2 as [[lo2 hi2]|]; [|discriminate]);
(lazymatch type of H with context [xhiB bc ?l] => destruct (xhiB bc l) as [h2|] eqn:Eh; [|discriminate] end);
unfold prune1pcK; cbv zeta;
(lazymatch goal with |- context [ranges_apart_pcB _ _ _ _ _ _ ?b ?k ?l] =>
rewrite (GEN b k l lo2 hi2 h2 ltac:(intros ? ?; discriminate) Eh H) end); reflexivity.
Qed.
Lemma hv_other_verdictJ : ltac2:(TCodec.tc2 tcn__FxCarry "RA'R4'?'UH%211%411'T;'Q0'C&Q2%2211%911'<'ZI%211%7221%411'G&VO%A11&W0r2%211(6%@2>?%A21@(Br6r5%34DD21r4%54EF21r3%749H21%;291%B3@=1&[>&XNr;r:%3221%?4LK1D%63K1:'8&[A&T?%118%3281(:%Q03621&W1r9r8%K4Q<Q<21r7%M4Q=Q>21%N4Q0Q?1M%Q22Q01%821C(E%Q;3A21&ZLr>r=%K221r<%5321L%QB3H18p081p0D1p0L1p0Q41pn<QJ1pj0QI1piFR11pi8R21p8R31p4R41pj>R31ph>R81po8R:1ph4R<1").
Proof.
intros X sx b gqj A0 B0 c0 d0 fl r HH Hin Hne HV.
destruct (hull_of_cov _ _ _ _ _ HH _ _ Hin) as (A & B & c & d & EA & EI & L1 & L2 & L3 & L4).
unfold verdictJ. cbn [si_sx mk_sxi]. rewrite Hne. change (si_abj (mk_sxi X sx)) with (si_abj (mk_sxi X sx)) in EA.
cbn [si_abj mk_sxi] in EA. cbn [si_abj mk_sxi]. rewrite EA.
unfold hv_other in HV. destruct gqj as [[gl gh]|]; [|discriminate].
destruct (PrimInt63.leb A0 gl) eqn:E.
- apply ileb_le in E. rewrite (ileb_true A gl) by lia. reflexivity.
- apply ileb_le in HV. destruct (PrimInt63.leb A gl); [reflexivity|]. apply ileb_true. lia.
Qed.
Definition ssvJ (s t : sxi) : bool :=
match si_abj t, si_eabj s with
| Some (A, B), Some (el, eh) => if PrimInt63.leb A el then true else PrimInt63.leb eh B
| _, _ => false
end.
Definition skipS5 (bc : bctx) (s t : sxi) : bool :=
if Pos.eqb (sx_bid (si_sx s)) (sx_bid (si_sx t)) then
match si_iv s with Some (a, e) => nonov t a e | None => false end
else if ssvJ s t then true
else in_sides_num bc (sp_D (sx_sp (si_sx s))) (a_base (sx_a (si_sx t))) (a_off (sx_a (si_sx t))) (sx_m1 (si_sx t)).
Definition hs_other (h : option hull) (el eh : int) : bool :=
match h with Some (A0, B0, _, _) => if PrimInt63.leb A0 el then true else PrimInt63.leb eh B0 | None => false end.
Fixpoint sb_pop (l : list sbe) (b : positive) : list sbe :=
match l with
| [] => []
| e :: r => (if Pos.eqb b (sbe_b e) then SBE (sbe_b e) (match sbe_fl e with [] => [] | _ :: tl => tl end) (sbe_h e) else e) :: sb_pop r b
end.
Fixpoint stores_partF5 (bc : bctx) (sis : list sxi) (R : list sbe) : list kentry :=
match sis with
| [] => []
| si :: newer =>
let sx := si_sx si in
let b := sx_bid sx in
let R' := sb_pop R b in
stores_partF5 bc newer R' ++
(let gen := fun _ : unit => chainKFF2 bc (si_bx si) (mk_flG (skipS5 bc si) newer) (KWord (sx_a sx) (sx_w sx) (sx_v sx))
(Some (a_base (sx_a sx))) (Pos.eqb b) (sx_br sx) None in
match si_iv si, si_eabj si with
| Some (a, e), Some (el, eh) =>
if forallbF (fun e' => if Pos.eqb b (sbe_b e') then true else hs_other (sbe_h e') el eh) R'
then match sb_find R' b with
| Some se => chainKI bc (si_bx si) (sbe_fl se) a e (KWord (sx_a sx) (sx_w sx) (sx_v sx))
(Some (a_base (sx_a sx))) (Pos.eqb b) (sx_br sx)
| None => gen tt
end
else gen tt
| _, _ => gen tt
end)
end.
Lemma disj_sidesB_in : ltac2:(TCodec.tc2 tcn__FxCarry "QE'RM'<'QL%211'QJ'N'R5&[>'C%1235(Br2r1%347921&S5r7r6r5r4r3%6554321%>3<81'H'F'J(QC%14?>98r9%E3J21%44<;BA%G3L13%7231'G'8&T<r:r8%3621FEJI(E%73621%A291qm0Q51%D2Q61qi6Q51%F2Q61p0H1plNQ:1pi4Q91pm8Q;1pkFQ<1ph>Q>1pl2Q@1phFQD1").
Proof.
intros bc kd b k n c m. induction kd as [|K rest IH]; intros H; [destruct H|].
assert (REC : In (c, m) (disj_sidesB bc rest b k n) ->
exists c' m', (In (KDisj c' m' c m) (K :: rest) \/ In (KDisj c m c' m') (K :: rest)) /\ sub_itvB bc b k n c' m' = true).
{ intros H0. destruct (IH H0) as (c' & m' & [HI|HI] & HS); exists c', m'; (split; [|exact HS]); [left|right]; right; exact HI. }
destruct K as [a w' v|a len|a len bk|lo hi|e' m'|e' lo' hi'|a en|c1 m1 c2 m2|a len fc|a len]; cbn [disj_sidesB] in H; try exact (REC H).
destruct (sub_itvB bc b k n c1 m1) eqn:E1; destruct (sub_itvB bc b k n c2 m2) eqn:E2; cbn [In] in H.
- destruct H as [E|[E|H]]; [injection E as <- <-; exists c1, m1; split; [left; left; reflexivity|exact E1]
|injection E as <- <-; exists c2, m2; split; [right; left; reflexivity|exact E2]|exact (REC H)].
- destruct H as [E|H]; [injection E as <- <-; exists c1, m1; split; [left; left; reflexivity|exact E1]|exact (REC H)].
- destruct H as [E|H]; [injection E as <- <-; exists c2, m2; split; [right; left; reflexivity|exact E2]|exact (REC H)].
- exact (REC H).
Qed.
Lemma disj_sidesB_intro : ltac2:(TCodec.tc2 tcn__FxCarry "QE'RM'<'QL%211'QJ'N'R5&[>(QCr4r3r2r1%544321r8%83=21'F'G'8&T<r:r7r6r5%564:321?(E%93821'C%12FH(B%14HJED&S5r;r9%352>1D=%L3751p0:1%B6AG@?KJ%E3D1=%:4Q1Q3A@%Q13<16p031%J261p0L1pm4Q81pi<Q71pm2Q:1pi:Q91pm8Q;1pkFQ<1ph>Q>1pl2Q@1phFQD1").
Proof.
intros bc kd b k n c1 m1 c2 m2. induction kd as [|K rest IH]; intros H; [destruct H|].
destruct H as [->|H].
- cbn [disj_sidesB]. split; intros E; rewrite E.
+ left. reflexivity.
+ destruct (sub_itvB bc b k n c1 m1); [right; left; reflexivity|left; reflexivity].
- destruct (IH H) as [I1 I2].
destruct K as [a w' v|a len|a len bk|lo hi|e' m'|e' lo' hi'|a en|d1 p1 d2 p2|a len fc|a len]; cbn [disj_sidesB]; try (split; assumption).
split; intros E; destruct (sub_itvB bc b k n d1 p1); destruct (sub_itvB bc b k n d2 p2); cbn [In]; auto.
Qed.
Lemma in_sidesB_intro : ltac2:(TCodec.tc2 tcn__FxCarry "Q7'RM'<'C'R5'QJ%3221%511'N&[>(Br2r1%349821r6%63921'G'8&T<r8r5r4r3%5649321<(E%93821&SBr9r7%352:1?9%>3=16p061p0A1plNL1pi4N1pm8K1pkFL1ph>Q01pRFO1phFQ61").
Proof.
intros bc D b k n c m. induction D as [|[c0 m0] r IH]; intros H E; [destruct H|]. cbn [in_sidesB].
destruct H as [H|H]; [injection H as -> ->; rewrite E; reflexivity|]. destruct (sub_itvB bc b k n c0 m0); [reflexivity|exact (IH H E)].
Qed.
Lemma in_sides_num_ex : ltac2:(TCodec.tc2 tcn__FxCarry "Q:'RM'<'C'R5'QJ%3221%511'N'G'8&W;r5r4r3r2r1%6554321(E%:3921'H'F&[>(B%14DC98r7%43D21&T<r8r6%3621BA?>%F3E1=%;261qlNL1%>2M1qi4O1%@2Q01p0B1pm8N1pkFO1ph>Q31pRFQ21phFQ91").
Proof.
intros bc D b k n. induction D as [|[c0 m0] r IH]; cbn [in_sides_num]; [discriminate|].
destruct (num_sub bc b k n c0 m0) eqn:E.
- intros _. exists c0, m0. split; [left; reflexivity|]. unfold num_sub in E. unfold sub_itvB. cbv [andb].
destruct (if expr_eqb b (a_base c0) then Z.leb (a_off c0) k else false); [|discriminate]. rewrite E. reflexivity.
- intros H. destruct (IH H) as (c & m & HI & HS). exists c, m. split; [right; exact HI|exact HS].
Qed.
Lemma sym_sides : ltac2:(TCodec.tc2 tcn__FxCarry "Q4'RM'<'QL%211'QJ'N'G'8&W;r8&S5r7r6r5r4%5564321r3r2r1%;5:4321(E%?3>21&SBr9%>51?:87%3521>=<%D3C16p061pmJG1pl<H1pi2J1pmHJ1pl:K1pi0M1pl2O1phFQ31").
Proof.
intros bc kd bs ks ns bt kt nt H. destruct (in_sides_num_ex _ _ _ _ _ H) as (c & m & HI & HT).
destruct (disj_sidesB_in _ _ _ _ _ _ _ HI) as (c' & m' & [HF|HF] & HS).
-
apply (in_sidesB_intro bc _ bs ks ns c' m'); [|exact HS]. exact (proj2 (disj_sidesB_intro bc kd bt kt nt c' m' c m HF) HT).
- apply (in_sidesB_intro bc _ bs ks ns c' m'); [|exact HS]. exact (proj1 (disj_sidesB_intro bc kd bt kt nt c m c' m' HF) HT).
Qed.
Lemma sym_keep : ltac2:(TCodec.tc2 tcn__FxCarry "QN'RM'T;'G'R<&TBr2%211&SMr3&QG&T>%116%311&QH%113&QI&TD%11<%311%<4;751%B3A>1r4%?41:84%E3DA1'8&W;r5&R9%H17%211%D1F%F11%C12&TA%11J%:596431(E%Q33=21'T4&T7r6%O1D%J1E&TC%11G(QD%Q41D%O1E%51F%43321(:&T@%11J%>8=I<;9431(RG%QE3A21p0C1p0Q21p0Q61po<QJ1pn@QK1phFQM1").
Proof.
intros bc s t Hs Ht H. rewrite Hs in H. cbn [sp_D mk_sprepB elen] in H. unfold sx_m1 in H. apply sym_sides in H.
destruct (sx_a s) as [kb kk] eqn:Ea. cbn [a_base a_off] in H. unfold prune1pcK. cbv zeta. unfold ranges_apart_pcB, elen. cbv zeta.
rewrite Ht at 2. cbn [sp_D mk_sprepB elen]. rewrite H.
destruct (match sp_rng (sx_sp t) with Some (lo1, hi1) => _ | None => false end); reflexivity.
Qed.
Lemma ssvJ_keep : ltac2:(TCodec.tc2 tcn__FxCarry "QF'RM'R4'?'UH%211%411'T;'G'8&ZC&XNr3r2%3221r1%5241%7231(E%;3:21&[A&T?%11:%21:%4221(:%B3A21'T4&T7r6&TB%11C&T>%11E&TD%11G&TC%11I(QDr4%811%712%613%53321&T@%116%B8A?=;93E1(RG%Q83E21p0G1p0O1po<Q<1pn@Q=1ph4Q?1phFQE1").
Proof.
intros bc X s t H Hne. unfold ssvJ in H. cbn [si_abj si_eabj mk_sxi] in H.
destruct (mk_abj (sp_rng (sx_sp t)) (iv_of (a_off (sx_a t)) (Z.of_nat (sx_w t)))) as [[A B]|] eqn:EAt; [|discriminate].
destruct (obr_eqb (sx_br s) (sp_rng (sx_sp s))) eqn:EO; [|discriminate]. apply obr_eqb_eq in EO.
destruct (mk_abj (sp_rng (sx_sp s)) (iv_of (a_off (sx_a s)) (Z.of_nat (sx_w s)))) as [[As Bs]|] eqn:EAs; [|discriminate].
apply mk_abj_val in EAt. destruct EAt as (lo1 & hi1 & Et & EA & EB & Hwt).
apply mk_abj_val in EAs. destruct EAs as (lo2 & hi2 & Es & EAs & EBs & Hws).
rewrite Es in EO.
destruct (sx_a s) as [kb kk] eqn:Ea. cbn [a_off] in *. unfold prune1pcK. cbv zeta. unfold ranges_apart_pcB, elen. cbv zeta. rewrite Et, EO.
rewrite (zlit64_small (Z.of_nat (sx_w t))) by lia. rewrite (zlit64_small (Z.of_nat (sx_w s))) by lia.
destruct (PrimInt63.leb A Bs) eqn:L.
- apply ileb_le in L. destruct (Z.leb_spec (hi1 + a_off (sx_a t) + Z.of_nat (sx_w t)) (lo2 + kk)); [reflexivity|lia].
- apply ileb_le in H. destruct (Z.leb (hi1 + a_off (sx_a t) + Z.of_nat (sx_w t)) (lo2 + kk)); [reflexivity|]. cbn [orb].
destruct (Z.leb_spec (hi2 + kk + Z.of_nat (sx_w s)) (lo1 + a_off (sx_a t))); [reflexivity|lia].
Qed.
Lemma sb_pop_ok : ltac2:(TCodec.tc2 tcn__FxCarry "J'<'ZI%211'Z0%411&U=r4(9r3r2%33921r1%73621r5&YO&T?&Z<%11;%311%52:1%?37<1p091pS4B1pmFE1pnLG1ph<G1").
Proof.
intros all si newer R. induction R as [|e r IH]; intros H; [intros e []|].
cbn [sb_pop]. intros e' [<-|Hin].
- destruct (H e (or_introl eq_refl)) as [HOK HFL].
destruct (Pos.eqb_spec (sx_bid (si_sx si)) (sbe_b e)) as [Eb|NE].
+ split; [exact HOK|]. cbn [sbe_fl sbe_b]. rewrite HFL. cbn [mk_flG]. unfold osame at 1. rewrite <- Eb, Pos.eqb_refl. reflexivity.
+ split; [exact HOK|]. rewrite HFL. cbn [mk_flG]. unfold osame at 1.
destruct (Pos.eqb_spec (sbe_b e) (sx_bid (si_sx si))) as [Eb|_]; [exfalso; apply NE; symmetry; exact Eb|reflexivity].
- apply IH; [|exact Hin]. intros e0 H0. apply H. right. exact H0.
Qed.
Lemma sb_pop_bases : ltac2:(TCodec.tc2 tcn__FxCarry "Q3'<'Z0%211'Q0&[>r1r3%33621'H'F&YOr5r4%3221%:3=91'G&Z1%11<%21<%43@21'?&VO%211&Z2%11C%21C%;3421%B281%C2>1qiHL1%F2M1p0H1piJO1ph>N1pS4Q01").
Proof.
induction R as [|x r IH]; intros b e0 Hin; [destruct Hin|]. cbn [sb_pop]. destruct Hin as [<-|Hin].
- eexists. split; [left; reflexivity|]. destruct (Pos.eqb b (sbe_b x)); split; reflexivity.
- destruct (IH b e0 Hin) as (e & H1 & H2). exists e. split; [right; exact H1|exact H2].
Qed.
Lemma stores_partF5_eq : ltac2:(TCodec.tc2 tcn__FxCarry "RA'RM'R4'?'UH%211%411'T1'<'ZI%211'T;%411'Z0%611&UAr6r5%3221'L&RIr7%2215r3%53=21&U=&M&XN%117r4%44CE21%63>18&[>r1r9%811%:4IK1D%53L41'H'F%83K7C'G'Q0&Z1%11;&T?&Z<%11H%311%83751%;2:1qiHQ61%>2Q71p0@1pnLQ=1r:%M11%O4Q>Q@1Q4%J3QAI1r2%L3QC1Jp031pnLQE1'QL%QH11&ZFr;%231:QC&T:%123Q@%M3631p091p0B1p0Q:1p0QB1p0QI1pS4QN1po:R11ph<R41poFR81ph4R:1phFR@1").
Proof.
intros bc X tt all sxs. induction sxs as [|sx rest IH]; intros R HX HSX HR HC HI; [reflexivity|].
pose proof (Forall_inv HSX) as HSX0. pose proof (Forall_inv_tail HSX) as HSXr.
cbn [map stores_partF5 stores_part]. cbv zeta.
assert (HR' : SBL_OK all (map (mk_sxi X) rest) (sb_pop R (sx_bid (si_sx (mk_sxi X sx))))) by (apply sb_pop_ok; exact HR).
assert (HC' : forall si, In si (map (mk_sxi X) rest) -> exists e, In e (sb_pop R (sx_bid (si_sx (mk_sxi X sx)))) /\ sbe_b e = sx_bid (si_sx si)).
{ intros si Hsi. destruct (HC si (or_intror Hsi)) as (e0 & He0 & Hb0).
destruct (sb_pop_bases R (sx_bid (si_sx (mk_sxi X sx))) e0 He0) as (e & H1 & H2 & _). exists e. split; [exact H1|congruence]. }
rewrite (IH _ HX HSXr HR' HC' (fun si Hsi => HI si (or_intror Hsi))). f_equal.
cbn [si_sx si_bx si_iv si_eabj mk_sxi].
assert (GEN : chainKFF2 bc (xget X (sx_bid sx)) (mk_flG (skipS5 bc (mk_sxi X sx)) (map (mk_sxi X) rest)) (KWord (sx_a sx) (sx_w sx) (sx_v sx))
(Some (a_base (sx_a sx))) (Pos.eqb (sx_bid sx)) (sx_br sx) None
= chainK2 bc rest (KWord (sx_a sx) (sx_w sx) (sx_v sx)) (Some (a_base (sx_a sx))) (Pos.eqb (sx_bid sx)) (sx_br sx)).
{ apply (chainKFF2_eqG2 bc X); [exact HX|apply HX| |exact I|].
- destruct (sx_a sx); reflexivity.
- intros t Hin Ht. unfold skipS5 in Ht. cbn [si_sx si_iv mk_sxi] in Ht.
destruct (Pos.eqb (sx_bid sx) (sx_bid t)) eqn:ES.
+ destruct (iv_of (a_off (sx_a sx)) (Z.of_nat (sx_w sx))) as [[a e]|] eqn:EIV; [|discriminate].
apply (nonov_keep bc X t _ a e _ _); [|exact Ht|].
* destruct (sx_a sx) as [kb kk]. exact EIV.
* destruct (sx_a sx) as [kb kk]. reflexivity.
+ left. symmetry. destruct (ssvJ (mk_sxi X sx) (mk_sxi X t)) eqn:EJ; [exact (ssvJ_keep bc X sx t EJ ES)|].
exact (sym_keep bc sx t (proj2 (proj2 HSX0)) (proj2 (proj2 (proj1 (Forall_forall _ _) HSXr t Hin))) Ht). }
destruct (iv_of (a_off (sx_a sx)) (Z.of_nat (sx_w sx))) as [[a e]|] eqn:EIV; [|exact GEN].
destruct (if obr_eqb (sx_br sx) (sp_rng (sx_sp sx))
then match mk_abj (sp_rng (sx_sp sx)) (Some (a, e)) with Some (A, B) => Some (B, A) | None => None end else None) as [[el eh]|] eqn:EE; [|exact GEN].
destruct (forallbF (fun e' => if Pos.eqb (sx_bid sx) (sbe_b e') then true else hs_other (sbe_h e') el eh)
(sb_pop R (sx_bid sx))) eqn:EALL; [|exact GEN].
destruct (sb_find (sb_pop R (sx_bid sx)) (sx_bid sx)) as [se|] eqn:ESB; [|exact GEN].
destruct (sb_find_in _ _ _ ESB) as [Hse Hseb]. destruct (HR' se Hse) as [_ HFL]. cbn [si_sx mk_sxi] in HFL. rewrite Hseb in HFL.
rewrite HFL, chainKI_eq.
apply (chainKFF2_eqG2 bc X); [exact HX|apply HX| |exact I|].
- destruct (sx_a sx); reflexivity.
- intros t Ht HSK. unfold osame in HSK. cbn [si_sx mk_sxi] in HSK.
destruct (Pos.eqb (sx_bid sx) (sx_bid t)) eqn:ES.
+ apply (nonov_keep bc X t _ a e _ _); [|exact HSK|].
* destruct (sx_a sx) as [kb kk]. exact EIV.
* destruct (sx_a sx) as [kb kk]. reflexivity.
+ left. symmetry. apply (ssvJ_keep bc X sx t); [|exact ES].
destruct (HC' (mk_sxi X t) (in_map _ _ _ Ht)) as (e' & He' & Hb'). cbn [si_sx mk_sxi] in Hb'.
pose proof (forallbF_in _ _ _ EALL e' He') as HV. cbv beta in HV. rewrite Hb', ES in HV.
destruct (HR' e' He') as [HOK _]. unfold SBE_OK in HOK. rewrite Hb' in HOK.
destruct (mk_flG_in (osame (sx_bid t)) all (mk_sxi X t) (HI _ (or_intror (in_map _ _ _ Ht)))) as [r Hr].
{ unfold osame. cbn [si_sx mk_sxi]. rewrite Pos.eqb_refl. reflexivity. }
rewrite HOK in HV. unfold hs_other in HV.
destruct (hull_of (mk_flG (osame (sx_bid t)) all)) as [[[[A0 B0] c0] d0]|] eqn:EH; [|discriminate].
destruct (hull_of_cov _ _ _ _ _ EH _ _ Hr) as (A & B & c & d & EA & _ & LA & LB & _ & _).
unfold ssvJ. rewrite EA. cbn [si_eabj mk_sxi]. rewrite EIV, EE.
destruct (PrimInt63.leb A0 el) eqn:L.
* apply ileb_le in L. rewrite (ileb_true A el) by lia. reflexivity.
* apply ileb_le in HV. destruct (PrimInt63.leb A el); [reflexivity|]. apply ileb_true. lia.
Qed.
Definition GSI (gs : gst) : Prop :=
(forall bid gk inner gid, pt_get (gs_gid gs) bid = Some inner -> pt_get inner gk = Some gid ->
Pos.lt gid (gs_next gs) /\ exists o lh, pt_get (gs_bnds gs) gid = Some (bid, o, lh)) /\
(forall gid v, pt_get (gs_bnds gs) gid = Some v -> Pos.lt gid (gs_next gs)).
Definition gmono (gs gs' : gst) : Prop :=
forall gid b o l h, pt_get (gs_bnds gs) gid = Some (b, o, (l, h)) ->
exists l' h', pt_get (gs_bnds gs') gid = Some (b, o, (l', h')) /\ l' <= l /\ h <= h'.
Lemma gmono_refl : ltac2:(TCodec.tc2 tcn__FxCarry "5'S>&VIr1%2211pj@41").
Proof. intros gs gid b o l h H. exists l, h. split; [exact H|lia]. Qed.
Lemma gmono_trans : ltac2:(TCodec.tc2 tcn__FxCarry "<'S>&VIr3r2%3221r5%5214p031p041pi491ph>:1ph6;1").
Proof.
intros a b c H1 H2 gid b0 o l h H. destruct (H1 _ _ _ _ _ H) as (l1 & h1 & E1 & L1 & L2).
destruct (H2 _ _ _ _ _ E1) as (l2 & h2 & E2 & L3 & L4). exists l2, h2. split; [exact E2|lia].
Qed.
Lemma GSI_empty : ltac2:(TCodec.tc2 tcn__FxCarry "3&TO&S?%211").
Proof.
split.
- intros bid gk inner gid H. cbn in H. rewrite pt_get_leaf in H. discriminate.
- intros gid v H. cbn in H. rewrite pt_get_leaf in H. discriminate.
Qed.
Lemma bnd_addF_ok : ltac2:(TCodec.tc2 tcn__FxCarry "RN'S>'Q0'?'C'N%2211%411'G&SA%711&R3&S;r9%211r8%53721(6%>2@;%?21=(Br3r2%34E@21r1%547C21%9271%C3A;1r4%E3K1>p031plFI1pmLI1ph>O1'F'R4%11Q2%211&S<&UGr7r6r5%46321?FE%611%715%Q63921&S=%115%219%Q:3Q@21'Hr:%>61Q8Q6=<;%Q:11%Q<3Q>1Q:%Q44QFQAQ9Q3%Q54QDQDQ3Q1%Q64Q8QD21%Q:2Q81%QD3QB51&[E%12Q8E%22EQ7%N221%O251qjLQM1%@2QN1ql>QO1%B2R01qmLQO1%D2R01&I%R13R7QAQ1%211%Q46QNQLQ3Q2Q1Q?%R011%R23R41QG%R33R5R0QH%R73R521p061pj2R?1&VI%12Q;Q8%QB231%QC2>1%QD2Q41%QE2Q91p0QG1pjNRD1plHRE1pmNRD1phJRJ1pj6RK1pj@RM1").
Proof.
intros gs gid bid obr lo hi HB. unfold bnd_addF.
destruct (pt_get (gs_bnds gs) gid) as [[[b o] [l h]]|] eqn:E.
- pose proof (HB _ _ _ eq_refl) as ->.
destruct (Z.leb l lo) eqn:L1'; [destruct (Z.leb hi h) eqn:L2'|];
[apply Z.leb_le in L1'; apply Z.leb_le in L2'|apply Z.leb_le in L1'; apply Z.leb_gt in L2'|apply Z.leb_gt in L1'].
+ split; [reflexivity|]. split; [reflexivity|]. split; [exists o, l, h; split; [exact E|lia]|]. split; [reflexivity|apply gmono_refl].
+ cbn [gs_gid gs_next gs_bnds]. split; [reflexivity|]. split; [reflexivity|].
split; [exists o, l, hi; rewrite pt_gss; split; [reflexivity|lia]|]. split; [intros g NE; apply pt_gso; exact NE|].
unfold gmono. cbn [gs_bnds]. intros g b0 o0 l0 h0 H0. destruct (Pos.eq_dec g gid) as [->|NE].
* rewrite E in H0. injection H0 as <- <- <- <-. exists l, hi. rewrite pt_gss. split; [reflexivity|lia].
* exists l0, h0. rewrite pt_gso by exact NE. split; [exact H0|lia].
+ cbn [gs_gid gs_next gs_bnds]. split; [reflexivity|]. split; [reflexivity|].
split; [exists o, lo, (if Z.leb hi h then h else hi); rewrite pt_gss; split; [reflexivity|destruct (Z.leb_spec hi h); lia]|].
split; [intros g NE; apply pt_gso; exact NE|].
unfold gmono. cbn [gs_bnds]. intros g b0 o0 l0 h0 H0. destruct (Pos.eq_dec g gid) as [->|NE].
* rewrite E in H0. injection H0 as <- <- <- <-. exists lo, (if Z.leb hi h then h else hi). rewrite pt_gss. split; [reflexivity|destruct (Z.leb_spec hi h); lia].
* exists l0, h0. rewrite pt_gso by exact NE. split; [exact H0|lia].
- cbn [gs_gid gs_next gs_bnds]. split; [reflexivity|]. split; [reflexivity|].
split; [exists obr, lo, hi; rewrite pt_gss; split; [reflexivity|lia]|]. split; [intros g NE; apply pt_gso; exact NE|].
unfold gmono. cbn [gs_bnds]. intros g b0 o0 l0 h0 H0. destruct (Pos.eq_dec g gid) as [->|NE]; [rewrite E in H0; discriminate|].
exists l0, h0. rewrite pt_gso by exact NE. split; [exact H0|lia].
Qed.
Lemma gstep_ok : ltac2:(TCodec.tc2 tcn__FxCarry "R8'S>'Q0'?'C'N%2211%411&TOr8%211'G%82:;&VFr9r7%33271(Br3r2%34BC21%:3951'F&UGr4r6r5%4693=<21%D11&VIr:%2214'H&SA%O11&R3&S;r<%?6=G18HM%311%5371I(6%Q62Q8Q3%Q721Q5%K4Q:Q57Jr1%M4Q9Q9K1%N45Q931%7251%Q63?91&[E%12Q0Q5%22Q;7%O221%Q0251qjLQB1%H2QC1ql>QD1%J2QE1qmLQD1%L2QE1%Q72N1%Q82Q21p0Q:1p0QF1pjDR01pj6R01pjNQN1plHQO1pmNQN1pj8R41phJR51pj@R71").
Proof.
intros gs bid gk obr lo hi gid gs0 [G1 G2] H. unfold ggroupK in H.
set (inner0 := match pt_get (gs_gid gs) bid with Some i => i | None => PTLeaf end) in *.
destruct (pt_get inner0 gk) as [g|] eqn:EG.
-
injection H as <- <-.
assert (HI : pt_get (gs_gid gs) bid = Some inner0).
{ unfold inner0 in *. destruct (pt_get (gs_gid gs) bid) as [i|]; [reflexivity|]. rewrite pt_get_leaf in EG. discriminate. }
destruct (G1 _ _ _ _ HI EG) as [L (o0 & lh0 & B0)].
assert (HB : forall b o lh, pt_get (gs_bnds gs) g = Some (b, o, lh) -> b = bid) by (intros b o lh E; rewrite B0 in E; injection E as <- _ _; reflexivity).
destruct (bnd_addF_ok gs g bid obr lo hi HB) as (E1 & E2 & E3 & E4 & E5).
split; [|split; [exact E5|exact E3]].
split.
+ intros bid' gk' inner gid' H1 H2. rewrite E1 in H1. rewrite E2. destruct (G1 _ _ _ _ H1 H2) as [L' (o' & lh' & B')].
split; [exact L'|]. destruct (Pos.eq_dec gid' g) as [->|NE].
* rewrite B0 in B'. injection B' as <- _ _. destruct E3 as (o3 & l3 & h3 & E3 & _). exists o3, (l3, h3). exact E3.
* exists o', lh'. rewrite (E4 _ NE). exact B'.
+ intros g' v Hv. rewrite E2. destruct (Pos.eq_dec g' g) as [->|NE]; [exact L|]. rewrite (E4 _ NE) in Hv. exact (G2 _ _ Hv).
-
injection H as <- <-.
set (gs0 := GST (pt_set bid (pt_set gk (gs_next gs) inner0) (gs_gid gs)) (Pos.succ (gs_next gs)) (gs_bnds gs)).
assert (HN : pt_get (gs_bnds gs) (gs_next gs) = None).
{ destruct (pt_get (gs_bnds gs) (gs_next gs)) as [v|] eqn:E; [|reflexivity]. pose proof (G2 _ _ E) as L. exfalso. exact (Pos.lt_irrefl _ L). }
assert (HB : forall b o lh, pt_get (gs_bnds gs0) (gs_next gs) = Some (b, o, lh) -> b = bid) by (intros b o lh E; cbn [gs0 gs_bnds] in E; rewrite HN in E; discriminate).
destruct (bnd_addF_ok gs0 (gs_next gs) bid obr lo hi HB) as (E1 & E2 & E3 & E4 & E5).
split; [|split; [exact E5|exact E3]].
split.
+ intros bid' gk' inner gid' H1 H2. rewrite E1 in H1. rewrite E2. cbn [gs0 gs_gid gs_next] in *.
assert (OLD : forall inner1, pt_get (gs_gid gs) bid' = Some inner1 -> pt_get inner1 gk' = Some gid' ->
Pos.lt gid' (Pos.succ (gs_next gs)) /\ exists o lh, pt_get (gs_bnds (bnd_addF gs0 (gs_next gs) bid obr lo hi)) gid' = Some (bid', o, lh)).
{ intros inner1 Q1 Q2. destruct (G1 _ _ _ _ Q1 Q2) as [L' (o' & lh' & B')]. split; [apply Pos.lt_lt_succ; exact L'|].
exists o', lh'. rewrite E4; [exact B'|]. intros ->. exact (Pos.lt_irrefl _ L'). }
destruct (Pos.eq_dec bid' bid) as [->|NEb].
* rewrite pt_gss in H1. injection H1 as <-.
destruct (Pos.eq_dec gk' gk) as [->|NEk].
-- rewrite pt_gss in H2. injection H2 as <-. split; [apply Pos.lt_succ_diag_r|].
destruct E3 as (o3 & l3 & h3 & E3 & _). exists o3, (l3, h3). exact E3.
-- rewrite pt_gso in H2 by exact NEk. unfold inner0 in H2.
destruct (pt_get (gs_gid gs) bid) as [i|] eqn:EI; [exact (OLD i eq_refl H2)|rewrite pt_get_leaf in H2; discriminate].
* rewrite pt_gso in H1 by exact NEb. exact (OLD inner H1 H2).
+ intros g' v Hv. rewrite E2. cbn [gs0 gs_next]. destruct (Pos.eq_dec g' (gs_next gs)) as [->|NE]; [apply Pos.lt_succ_diag_r|].
rewrite (E4 _ NE) in Hv. cbn [gs0 gs_bnds] in Hv. apply Pos.lt_lt_succ. exact (G2 _ _ Hv).
Qed.
Definition in_grp (gs : gst) (e : einfoF) : Prop :=
match ef_m e with
| Some _ => exists o l h, pt_get (gs_bnds gs) (ef_gid e) = Some (ef_bid e, o, (l, h)) /\ l <= ef_k e /\ ef_end e <= h
| None => True
end.
Definition in_grpo (gs : gst) (oi : option einfoF) : Prop := match oi with Some e => in_grp gs e | None => True end.
Lemma scanF_grp : ltac2:(TCodec.tc2 tcn__FxCarry "Q@'RM'<'QL%211'T1'S>'?'V;%211%811&TOr4%211'G'C%126;%221;&Z5r8r7r6r5%544321(Br3%24@E>1r2%44<F21%?3<61'F%D16&VI%12<8'L&W8%11;%33L1?%8251%9281p0;1p0L1pjBQ41po>Q61pk>Q21pj@Q71po<Q91pl8Q;1phFQ?1").
Proof.
intros bc kn. induction kn as [|K rest IH]; intros t gs infos t' gs' HG H.
- cbn in H. injection H as <- <- <-. split; [exact HG|]. split; [apply gmono_refl|constructor].
- cbn [scanF] in H. destruct (kdescrF K) as [[[kb kk] om]|].
+ destruct (intern bc t kb) as [[bid bi] t1].
destruct om as [m|].
* unfold ggroupF in H. destruct (ggroupK gs bid (gkeyF kk)) as [gid gs0] eqn:EG.
destruct (scanF bc rest t1 (bnd_addF gs0 gid bid (bi_br bi) kk (kk + m))) as [[infos2 t2] gs2] eqn:ES.
injection H as <- <- <-.
destruct (gstep_ok gs bid (gkeyF kk) (bi_br bi) kk (kk + m) gid gs0 HG EG) as (HG1 & HM1 & (o & l & h & E1 & L1 & L2)).
destruct (IH _ _ _ _ _ HG1 ES) as (HG2 & HM2 & HF).
split; [exact HG2|]. split; [exact (gmono_trans _ _ _ HM1 HM2)|].
constructor; [|exact HF]. cbn [in_grpo in_grp ef_m ef_gid ef_bid ef_k ef_end].
destruct (HM2 _ _ _ _ _ E1) as (l' & h' & E2 & L3 & L4). exists o, l', h'. split; [exact E2|lia].
* destruct (scanF bc rest t1 gs) as [[infos2 t2] gs2] eqn:ES. injection H as <- <- <-.
destruct (IH _ _ _ _ _ HG ES) as (HG2 & HM2 & HF).
split; [exact HG2|]. split; [exact HM2|]. constructor; [exact I|exact HF].
+ destruct (scanF bc rest t gs) as [[infos2 t2] gs2] eqn:ES. injection H as <- <- <-.
destruct (IH _ _ _ _ _ HG ES) as (HG2 & HM2 & HF).
split; [exact HG2|]. split; [exact HM2|]. constructor; [exact I|exact HF].
Qed.
Inductive sameb := SNone | SClean (fl : list (sxi * list sxi)) | SDirty (fl : list (sxi * list sxi)).
Record grp6 := GRP6 { k_flo : list (sxi * list sxi); k_fl : list (sxi * list sxi); k_same : sameb }.
Definition mk_glF6 (bc : bctx) (info : ptree binfo) (X : ptree (option bx)) (bnds : gtab) (sis : list sxi) (sbl : list sbe) : ptree (option grp6) :=
pt_map (fun g : gval =>
match g with
| (b, _, (glo, ghi)) =>
match pt_get info b with
| Some bi =>
let gx := if is_litb (bi_base bi) then None else Some (GXI (bi_base bi) (xget X b)) in
let gqj := gqj_of (match bi_br bi with Some (lo2, hi2) => Some (glo + lo2, ghi + hi2) | None => None end) in
let flo := if forallbF (fun e => if Pos.eqb b (sbe_b e) then true else hv_other (sbe_h e) gqj) sbl then []
else mk_flM bc b glo ghi gx gqj true [] sis in
Some (GRP6 flo
(match flo with [] => [] | _ :: _ => mk_flM bc b glo ghi gx gqj false [] sis end)
(match sb_find sbl b with
| Some e => if hv_same (sbe_h e) (match z2b glo with Some a => match z2b ghi with Some e' => Some (a, e') | None => None end | None => None end)
then SClean (sbe_fl e) else SDirty (sbe_fl e)
| None => SNone
end))
| None => None
end
end) bnds.
Definition sameof (K : kentry) (ei : einfoF) : positive -> bool := match kbase K with Some _ => Pos.eqb (ef_bid ei) | None => fun _ => false end.
Definition br2of (K : kentry) (ei : einfoF) : option (Z * Z) := match kbase K with Some _ => ef_br ei | None => None end.
Fixpoint chainKP (bc : bctx) (xo : option bx) (fl : list (sxi * list sxi)) (a e : int) (K : kentry) (okb : option expr)
(same_of : positive -> bool) (br2 : option (Z * Z)) : list kentry :=
match fl with
| [] => [K]
| (si, rest) :: fl' =>
if nonov si a e then chainKP bc xo fl' a e K okb same_of br2 else
match prune1pcKX bc si xo K (same_of (sx_bid (si_sx si))) br2 None with
| PKeep => chainKP bc xo fl' a e K okb same_of br2
| PRepl l =>
match okb with
| Some kb =>
flat_map (fun K' => match kbase K' with
| Some kb' =>
if expr_eqb kb' kb then
match ent_iv K' with
| Some (a', e') =>
if (if PrimInt63.leb a a' then PrimInt63.leb e' e else false)
then chainKP bc xo fl' a' e' K' okb same_of br2
else chainK2F2 bc xo rest K' okb same_of br2 None
| None => chainK2F2 bc xo rest K' okb same_of br2 None
end
else chain_slowF bc rest [K']
| None => chain_slowF bc rest [K']
end) l
| None => chain_slowF bc rest l
end
end
end.
Definition PREM (bc : bctx) (X : ptree (option bx)) (p : sxi -> bool) (okb : option expr) (same_of : positive -> bool) (br2 : option (Z * Z))
(sxs : list stx) (a e : int) : Prop :=
forall K' a' e', kbase K' = okb -> ent_iv K' = Some (a', e') -> toZ a <= toZ a' -> toZ e' <= toZ e ->
forall sx, In sx sxs -> (if p (mk_sxi X sx) then true else nonov (mk_sxi X sx) a' e') = true ->
pk_rel K' PKeep (prune1pcK bc (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) K' (same_of (sx_bid sx)) br2).
Lemma chainKP_eq : ltac2:(TCodec.tc2 tcn__FxCarry "RB'RM'R4'?'UH%211%411'ZI'8p021'QJ%811'Q0p015'C'N%2211%>11'<'T;%211&Q2'QL&UAr;r:%3221&TLr<%2214&U;r=r9r8r7r6r5r4%897:=654321'G&QK%114%33O1A%M2FF%Q911&V>%11:(6(B%14LL?>%3271%<3751%Q21N&V5r@r>&X9&M&XNr?%211%44Q:QF1M%62O1%:9981NMLQ3Q7Q6&S2%16;Q1NQ5Q9Q8%K3>31p0@1p0J1p0O1p0Q91p0Q=1pRLQB1piHQD1ph6QE1po:QG1phNQK1pnDR01pn0R31pn2R61pQP2R;1ph4R;1phFRA1").
Proof.
intros bc X xo p okb same_of br2 sxs. induction sxs as [|sx rest IH]; intros a e K HX Hxo HP HK HI; [reflexivity|].
assert (HP' : forall a' e', toZ a <= toZ a' -> toZ e' <= toZ e -> PREM bc X p okb same_of br2 rest a' e').
{ intros a' e' L1 L2 K' a'' e'' H1 H2 L3 L4 sx' Hin HS. apply (HP K' a'' e'' H1 H2); [lia|lia|right; exact Hin|exact HS]. }
assert (IH' : chainKP bc xo (mk_flG p (map (mk_sxi X) rest)) a e K okb same_of br2 = chainK2 bc rest K okb same_of br2)
by (apply IH; [exact HX|exact Hxo|apply HP'; lia|exact HK|exact HI]).
assert (SKIP : (if p (mk_sxi X sx) then true else nonov (mk_sxi X sx) a e) = true ->
chainK2 bc (sx :: rest) K okb same_of br2 = chainK2 bc rest K okb same_of br2).
{ intros HS. cbn [chainK2].
destruct (HP K a e HK HI ltac:(lia) ltac:(lia) sx (or_introl eq_refl) HS) as [E|[_ E2]].
- rewrite <- E. reflexivity.
- rewrite E2. destruct okb as [kb|].
+ cbn [flat_map]. rewrite HK, p_expr_eqb_refl, app_nil_r. reflexivity.
+ apply chain_slow_nobase. exact HK. }
cbn [map mk_flG].
destruct (p (mk_sxi X sx)) eqn:EP; [rewrite (SKIP eq_refl); exact IH'|].
cbn [chainKP]. destruct (nonov (mk_sxi X sx) a e) eqn:EN; [rewrite (SKIP eq_refl); exact IH'|].
cbn [chainK2]. rewrite prune1pcKX_eq. cbn [si_sx si_bx mk_sxi].
destruct (prune1pcKF2_rel bc (xget X (sx_bid sx)) xo (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) K (same_of (sx_bid sx)) br2 None (HX (sx_bid sx)) Hxo I)
as [E|[E1 E2]].
- rewrite E. destruct (prune1pcK _ _ _ _ _ K _ br2) as [|l]; [exact IH'|].
destruct okb as [kb|]; [|(rewrite chain_slowF_eq; reflexivity)].
apply flat_map_ext_in. intros K' _. destruct (kbase K') as [kb'|] eqn:HB; [|(rewrite chain_slowF_eq; reflexivity)].
destruct (expr_eqb kb' kb) eqn:EQ; [|(rewrite chain_slowF_eq; reflexivity)].
apply p_expr_eqb_eq in EQ. subst kb'.
destruct (ent_iv K') as [[a' e']|] eqn:EI'; [|apply chainK2F2_eq; [exact HX|exact Hxo|symmetry; exact HB|exact I]].
destruct (if PrimInt63.leb a a' then PrimInt63.leb e' e else false) eqn:EC; [|apply chainK2F2_eq; [exact HX|exact Hxo|symmetry; exact HB|exact I]].
destruct (PrimInt63.leb a a') eqn:L1; [|discriminate]. apply ileb_le in L1. apply ileb_le in EC.
apply IH; [exact HX|exact Hxo|apply HP'; assumption|exact HB|exact EI'].
- rewrite E1, E2, IH'.
destruct okb as [kb|].
+ cbn [flat_map]. rewrite HK, p_expr_eqb_refl, app_nil_r. reflexivity.
+ symmetry. apply chain_slow_nobase. exact HK.
Qed.
Lemma ent_iv_kdescr : ltac2:(TCodec.tc2 tcn__FxCarry "QL'QL&Q2'G'?'C%1244%311&V>r3%211(6(Br2r1%34==21%52:1%>3:71'H'QJ'N'F%A232%C13%C221%E11&SEr7%211%A4:9D@%C2:@%C49821%E281%N3851&Q8r6%211&[C&[M+2+QK%3221%52M1%Q83G71r5%;11%92Q1Q0%:216%Q=3L31%L261%M2A1qlNO1%Q22Q01ql4Q11%Q42Q21ql0Q41%Q62Q51p0Q81piHQH1ph6QI1pRLQK1").
Proof.
intros K a e HI.
assert (G : forall kb kk m, kdescr K = Some (kb, kk, Some m) -> exists kb kk m, kdescr K = Some (kb, kk, Some m) /\ toZ a = kk + 2 ^ 59 /\ toZ e = kk + m + 2 ^ 59).
{ intros kb kk m HD. exists kb, kk, m. split; [exact HD|]. exact (ent_iv_descr _ _ _ _ _ _ HI HD). }
destruct K as [[b k] w' v|[b k] len|[b k] len bk|lo hi|e' m'|e' lo' hi'|[b k] n|a1 n1 a2 n2|[b k] len fc|[b k] len];
cbn [ent_iv] in HI; try discriminate.
- eapply G. reflexivity.
- destruct len as [l0| | | | | | |]; try discriminate. eapply G. reflexivity.
- destruct len as [l0| | | | | | |]; try discriminate. eapply G. reflexivity.
- destruct (Z.ltb_spec lo hi) as [Hlh|]; [|discriminate].
destruct (z2b lo) as [a'|] eqn:Ea; [|discriminate]. destruct (z2b hi) as [e''|] eqn:Ee; [|discriminate].
apply z2b_val in Ea. apply z2b_val in Ee. eapply G. cbn [kdescr].
destruct (Z.ltb_spec (hi - lo) (2 ^ 64)); [reflexivity|lia].
- destruct len as [l0| | | | | | |]; try discriminate. eapply G. reflexivity.
- destruct len as [l0| | | | | | |]; try discriminate. eapply G. reflexivity.
Qed.
Section GrpKeep.
Variables (bc : bctx) (X : ptree (option bx)) (t : ntab) (sxs : list stx).
Hypotheses (HX : XOK bc X) (HT : NTI bc t) (HS : Forall (SX_OK bc t) sxs).
Variables (bid : positive) (kb : expr) (glo ghi : Z).
Hypothesis HIn : In (kb, bid) (nt_bucket t (bkey kb)).
Let obr := base_rangeB bc kb.
Let gx := if is_litb kb then None else Some (GXI kb (xget X bid)).
Let gqj := gqj_of (match obr with Some (lo2, hi2) => Some (glo + lo2, ghi + hi2) | None => None end).
Definition prG (K' : kentry) (sx : stx) : pk_res :=
prune1pcK bc (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) K'
(match kbase K' with Some _ => Pos.eqb bid | None => fun _ => false end (sx_bid sx))
(match kbase K' with Some _ => obr | None => None end).
Lemma grp_keepJ : ltac2:(TCodec.tc2 tcn__FxCarry "QM'QL'N'T;'G'?'C'QJ%2216%417%4221%611&SEr4%211(6(Bv]Or3%34<A21r2%62C1%64>=31%82=1%D3=:1&[Ev]4%221>&[Cr5%221Av]1%7221&[>v_D%23Q0F1'8&ZL&XNv\1%221;v\<v]6%63321(E%Q93921'T4&U0r9r6%3221(RG%Q@3621p081p0C1p0G1p0M1p0Q11po8QG1pm0QI1pl6QJ1pRNQL1").
Proof.
intros K' kk' m' sx HD Hlo Hhi Hsx EV. unfold prG.
set (ei' := EI bid xH kb obr kk' (Some m')).
assert (Hinb : inb (bid, obr, (glo, ghi)) ei' = true).
{ unfold inb. cbn [ei' ei_m ei_bid ei_br ei_k]. rewrite Pos.eqb_refl, obr_eqb_refl.
apply Z.leb_le in Hlo. rewrite Hlo. cbn [andb]. apply Z.leb_le. exact Hhi. }
assert (HK' : EINF bc t K' (Some ei')) by (cbn [EINF ei' ei_kb ei_k ei_m ei_bid ei_br]; exact (conj HD (conj HIn eq_refl))).
unfold gqj in EV. apply verdictJ_F in EV.
change (match obr with Some (lo2, hi2) => Some (glo + lo2, ghi + hi2) | None => None end) with (gq_of (bid, obr, (glo, ghi))) in EV.
rewrite verdictF_eq in EV.
exact (verdict_keepG bc t sx _ ei' K' HT (proj1 (Forall_forall _ _) HS sx Hsx) HK' Hinb EV).
Qed.
Lemma grp_keepV : ltac2:(TCodec.tc2 tcn__FxCarry "QO'QL'N'T;'G'?'C'QJ%2216%417%4221%611&SEr4%211(6(Bv]Or3%34<A21r2%62C1%64>=31%82=1%D3=:1&[Ev]4%221>&[Cr5%221Av]1%7221&[>v_D%23Q0F1'8&Z?v\:v\<v]<v]6&XNv\1%221?%8776C>541(E%Q;3;21'T4&U0r9r6%3221(RG%QB3621p081p0E1p0I1p0O1p0Q31po8QI1pm0QK1pl6QL1pRNQN1").
Proof.
intros K' kk' m' sx HD Hlo Hhi Hsx HSK. unfold skipv5 in HSK.
destruct (verdictJ (mk_sxi X sx) bid gqj) eqn:EV; [exact (grp_keepJ K' kk' m' sx HD Hlo Hhi Hsx EV)|].
unfold gx in HSK. destruct (is_litb kb) eqn:Hlit; [unfold linV2 in HSK; discriminate|].
apply (linV2_linV _ _ _ obr) in HSK. unfold prG.
set (ei' := EI bid xH kb obr kk' (Some m')).
assert (Hinb : inb (bid, obr, (glo, ghi)) ei' = true).
{ unfold inb. cbn [ei' ei_m ei_bid ei_br ei_k]. rewrite Pos.eqb_refl, obr_eqb_refl.
apply Z.leb_le in Hlo. rewrite Hlo. cbn [andb]. apply Z.leb_le. exact Hhi. }
refine (linV_keep bc X sx bid obr glo ghi (GXI kb (xget X bid)) K' ei' HX (HX _) Hlit _ Hinb HSK).
unfold member_ok. rewrite HD. cbn [gx_b]. rewrite p_expr_eqb_refl.
apply Z.leb_le in Hlo. rewrite Hlo. apply Z.leb_le. exact Hhi.
Qed.
Lemma grp_oth : forall sbl K' kk' m' sx,
SBL_OK (map (mk_sxi X) sxs) (map (mk_sxi X) sxs) sbl ->
(forall si, In si (map (mk_sxi X) sxs) -> exists e, In e sbl /\ sbe_b e = sx_bid (si_sx si)) ->
(if forallbF (fun e => if Pos.eqb bid (sbe_b e) then true else hv_other (sbe_h e) gqj) sbl then []
else mk_flG (skipo5 bc bid glo ghi gx gqj) (map (mk_sxi X) sxs)) = [] ->
kdescr K' = Some (kb, kk', Some m') -> glo <= kk' -> kk' + m' <= ghi ->
In sx sxs -> Pos.eqb bid (sx_bid sx) = false -> prG K' sx = PKeep.
Proof.
intros sbl K' kk' m' sx HSB1 HSB2 EFLO HD Hlo Hhi Hsx Hne.
destruct (forallbF (fun e => if Pos.eqb bid (sbe_b e) then true else hv_other (sbe_h e) gqj) sbl) eqn:EALL.
- apply (grp_keepJ K' kk' m' sx HD Hlo Hhi Hsx).
destruct (HSB2 (mk_sxi X sx) (in_map _ _ _ Hsx)) as (se & Hse & Hseb). cbn [si_sx mk_sxi] in Hseb.
pose proof (forallbF_in _ _ _ EALL se Hse) as HV. cbv beta in HV. rewrite Hseb, Hne in HV.
destruct (HSB1 se Hse) as [HOK _]. unfold SBE_OK in HOK. rewrite Hseb in HOK.
destruct (mk_flG_in (osame (sx_bid sx)) (map (mk_sxi X) sxs) (mk_sxi X sx) (in_map _ _ _ Hsx)) as [r Hr].
{ unfold osame. cbn [si_sx mk_sxi]. rewrite Pos.eqb_refl. reflexivity. }
rewrite HOK in HV. destruct (hull_of (mk_flG (osame (sx_bid sx)) (map (mk_sxi X) sxs))) as [[[[A0 B0] c0] d0]|] eqn:EH; [|discriminate].
exact (hv_other_verdictJ X sx bid gqj A0 B0 c0 d0 _ r EH Hr Hne HV).
- apply (grp_keepV K' kk' m' sx HD Hlo Hhi Hsx).
pose proof (mk_flG_nil _ _ EFLO (mk_sxi X sx) (in_map _ _ _ Hsx)) as HSO.
unfold skipo5 in HSO. cbn [si_sx mk_sxi] in HSO. rewrite Hne in HSO. exact HSO.
Qed.
End GrpKeep.
Definition ksym (K : kentry) : option (expr * Z * expr) :=
match K with
| KZero (SA kb kk) len | KUnk (SA kb kk) len | KFill (SA kb kk) len _ | KBlob (SA kb kk) len _ =>
match len with ELit _ => None | _ => Some (kb, kk, len) end
| _ => None
end.
Fixpoint in_sidesXM (bc : bctx) (m : smemo) (D : list (saddr * expr)) (b : expr) (k : Z) (n : expr) : bool * smemo :=
match D with
| [] => (false, m)
| (c, e) :: r =>
match sm_find m c e with
| Some true => (true, m)
| Some false => in_sidesXM bc m r b k n
| None => if sub_itv_xB bc b k n c e then (true, (c, e, true) :: m) else in_sidesXM bc ((c, e, false) :: m) r b k n
end
end.
Definition MEMO_OKX (bc : bctx) (b : expr) (k : Z) (n : expr) (m : smemo) : Prop := forall c e r, In (c, e, r) m -> r = sub_itv_xB bc b k n c e.
Lemma sm_find_okX : ltac2:(TCodec.tc2 tcn__FxCarry "Q6'RM'QJ'N&ZA'R5'8&U6r8r7r6r5r4%6554321'G'?%11:&Z@r3%23871(6r2%22@1%93741&T=r:r9%3621CB@?%>3F:1p061p0A1pn<I1piHN1pi4L1plNN1pm8Q11pkFQ11ph>Q31phFQ51").
Proof.
intros bc b k n m c e r. induction m as [|[[c' e'] r'] rest IH]; intros H HF; [discriminate|]. cbn [sm_find] in HF. eF.
destruct (if expr_eqb (a_base c) (a_base c') then if Z.eqb (a_off c) (a_off c') then expr_eqb e e' else false else false) eqn:E.
- injection HF as <-. destruct (expr_eqb (a_base c) (a_base c')) eqn:E1; [|discriminate]. destruct (Z.eqb_spec (a_off c) (a_off c')) as [E2|]; [|discriminate].
apply p_expr_eqb_eq in E1. apply p_expr_eqb_eq in E. subst e'. destruct c as [cb co], c' as [cb' co']. cbn [a_base a_off] in *. subst cb' co'.
apply H. left. reflexivity.
- apply IH; [intros c0 e0 r0 H0; apply H; right; exact H0|exact HF].
Qed.
Lemma in_sidesXM_ok : ltac2:(TCodec.tc2 tcn__FxCarry "Q7'RM'<'C'R5'QJ%3221%511'N&ZA&U6r6r4r3r2r1%6554321'F'G'8&;&W:r7r5%362:=1<;%536@1&SC%155@4?>%:3931&D%13;E6%E598CB1%?241p0A1plNI1pm8N1pkFL1ph>Q01pRFO1phFQ61").
Proof.
intros bc D b k n. induction D as [|[c e] r IH]; intros m H; [split; [reflexivity|exact H]|].
cbn [in_sidesXM in_sides_xB]. destruct (sm_find m c e) as [[|]|] eqn:EF.
- rewrite <- (sm_find_okX bc b k n m c e true H EF). split; [reflexivity|exact H].
- rewrite <- (sm_find_okX bc b k n m c e false H EF). exact (IH m H).
- destruct (sub_itv_xB bc b k n c e) eqn:ES.
+ split; [reflexivity|]. intros c0 e0 r0 [E|H0]; [injection E as <- <- <-; symmetry; exact ES|exact (H c0 e0 r0 H0)].
+ apply IH. intros c0 e0 r0 [E|H0]; [injection E as <- <- <-; symmetry; exact ES|exact (H c0 e0 r0 H0)].
Qed.
Definition skipX (bc : bctx) (same_of : positive -> bool) (enj : option (PrimInt63.int * PrimInt63.int * option PrimInt63.int))
(sym : option (expr * Z * expr)) (si : sxi) : bool :=
if same_of (sx_bid (si_sx si)) then false
else if symnumJ si enj then true
else match sym with Some (b, k, n) => in_sides_xB bc (sp_Dx (sx_sp (si_sx si))) b k n | None => false end.
Fixpoint mk_flX (bc : bctx) (same_of : positive -> bool) (enj : option (PrimInt63.int * PrimInt63.int * option PrimInt63.int))
(sym : option (expr * Z * expr)) (m : smemo) (sis : list sxi) : list (sxi * list sxi) :=
match sis with
| [] => []
| si :: srest =>
if same_of (sx_bid (si_sx si)) then (si, srest) :: mk_flX bc same_of enj sym m srest
else if symnumJ si enj then mk_flX bc same_of enj sym m srest
else match sym with
| Some (b, k, n) =>
let '(v, m') := in_sidesXM bc m (sp_Dx (sx_sp (si_sx si))) b k n in
if v then mk_flX bc same_of enj sym m' srest else (si, srest) :: mk_flX bc same_of enj sym m' srest
| None => (si, srest) :: mk_flX bc same_of enj sym m srest
end
end.
Lemma mk_flX_eq : forall bc same_of enj sym sis m,
match sym with Some (b, k, n) => MEMO_OKX bc b k n m | None => True end ->
mk_flX bc same_of enj sym m sis = mk_flG (skipX bc same_of enj sym) sis.
Proof.
intros bc same_of enj sym sis. induction sis as [|si rest IH]; intros m H; [reflexivity|].
cbn [mk_flX mk_flG]. unfold skipX at 1.
destruct (same_of (sx_bid (si_sx si))); [rewrite (IH m H); reflexivity|].
destruct (symnumJ si enj); [exact (IH m H)|].
destruct sym as [[[b k] n]|]; [|rewrite (IH m H); reflexivity].
destruct (in_sidesXM_ok bc (sp_Dx (sx_sp (si_sx si))) b k n m H) as [E1 E2].
destruct (in_sidesXM bc m (sp_Dx (sx_sp (si_sx si))) b k n) as [v m']. cbn [fst snd] in E1, E2. rewrite <- E1.
rewrite (IH m' E2). reflexivity.
Qed.
Lemma sidesx_keep : ltac2:(TCodec.tc2 tcn__FxCarry "QK'RM'T;'QL'QJ'N'?'C%1233%311'G%4276%5218%711&WLr5%211(6(Br4r3%34A@21r2%54<C21%72<1%?3<91'8&SCr8&R:&TBr7%211%411%7561C?>(E%J3:21'T4&T7r9%:1<&T>%11>&TD%11@&TC%11B(:%:898642A1L(RG%Q83=21p0?1p0K1phNQ<1pm8QB1pkFQB1ph>QD1pRLQF1po8QH1phFQJ1").
Proof.
intros bc sx K b k n br2 HK HS.
assert (RAP : forall z1, ranges_apart_pcB bc (sx_sp sx) (a_base (sx_a sx)) (a_off (sx_a sx)) (ELit z1) br2 b k n = true).
{ intros z1. unfold ranges_apart_pcB.
destruct K as [[kb kk] w' v|[kb kk] len|[kb kk] len bk|lo hi|e' m'|e' lo' hi'|[eb ek] en|c1 m1 c2 m2|[kb kk] len fc|[kb kk] len];
cbn [ksym] in HK; try discriminate;
(destruct len as [z| | | | | | |]; [discriminate| ..]); injection HK as <- <- <-; rewrite HS;
match goal with |- (if ?c then true else true) = true => destruct c; reflexivity end. }
destruct K as [[kb kk] w' v|[kb kk] len|[kb kk] len bk|lo hi|e' m'|e' lo' hi'|[eb ek] en|c1 m1 c2 m2|[kb kk] len fc|[kb kk] len];
cbn [ksym] in HK; try discriminate;
(destruct len as [z| | | | | | |]; [discriminate| ..]); injection HK as <- <- <-;
unfold prune1pcK, elen; cbv zeta; rewrite RAP; reflexivity.
Qed.
Fixpoint entriesGF8 (bc : bctx) (X : ptree (option bx)) (sis : list sxi) (gl : ptree (option grp6))
(kn : list kentry) (infos : list (option einfoF)) : list kentry :=
match kn, infos with
| K :: rest, oi :: irest =>
(match oi with
| Some ei =>
match ef_m ei with
| Some _ =>
match pt_get gl (ef_gid ei) with
| Some (Some g) =>
match k_flo g with
| [] => match k_same g with
| SNone => [K]
| SClean fl => match ent_iv K with
| Some _ => [K]
| None => chainKFF2 bc (xget X (ef_bid ei)) fl K (kbase K) (sameof K ei) (br2of K ei) None
end
| SDirty fl => match ent_iv K with
| Some (a, e) => chainKP bc (xget X (ef_bid ei)) fl a e K (kbase K) (sameof K ei) (br2of K ei)
| None => chainKFF2 bc (xget X (ef_bid ei)) fl K (kbase K) (sameof K ei) (br2of K ei) None
end
end
| _ :: _ => chainKFF2 bc (xget X (ef_bid ei)) (k_fl g) K (kbase K) (sameof K ei) (br2of K ei) None
end
| _ => chainK2F2 bc (xget X (ef_bid ei)) sis K (kbase K) (sameof K ei) (br2of K ei) None
end
| None =>
let p := mk_pre bc K (br2of K ei) in
let enj := enj_of K (br2of K ei) (fst p) (snd p) in
chainKFF2 bc (xget X (ef_bid ei)) (mk_flX bc (sameof K ei) enj (ksym K) [] sis)
K (kbase K) (sameof K ei) (br2of K ei) (Some p)
end
| None => if is_fact_entry K then [K] else chainK2F2 bc None sis K None (fun _ => false) None None
end) ++ entriesGF8 bc X sis gl rest irest
| _, _ => []
end.
Lemma entriesGF8_C : ltac2:(TCodec.tc2 tcn__FxCarry "R@'RM'R4'?'UH%211%411'T1'<'T;%211'S>'QL%511'V;%<11%811&UAr7r6%3221&RFr8%2214'L&RIr9%2219%43C19'[=&TMr:%221:r5r4%65GD321&W8%11C%>3G15'G&V@r<r;&M'ZI&XN%114%44Q631E&X<&T0%11C&S;%11N&XB(>'Z0%211%43::1%:6A8@6;1%C6BA<1Q9Q8&V='S7%QK11&@&V9%23QC41%G4QC41Q?%74JQ9QA1%M3QG91p0O1p0Q31p0Q;1p0QA1p0QE1pk>QJ1pl8QN1pj@R11po:R31po<R71ph4R91phFR?1").
Proof.
intros bc X t sxs gs kn infos HX HT HS HF HG.
set (sis := map (mk_sxi X) sxs).
assert (SBL0 : SBL_OK sis sis []) by (intros e []).
destruct (mk_sbl_ok sis sis [] SBL0) as (HSB1 & HSB2 & _).
set (sbl := mk_sbl sis sis []) in *.
induction HF as [|K oi rest irest HK HF IH]; [reflexivity|].
pose proof (Forall_inv HG) as HG0. specialize (IH (Forall_inv_tail HG)).
cbn [entriesGF8 entC map]. rewrite IH. f_equal.
destruct oi as [ei|].
- cbn [option_map ei_bid ei_br ef_ei]. destruct HK as [HK HE]. unfold sameof, br2of.
destruct (ef_m ei) as [m|] eqn:Hm.
2:{ rewrite mk_flX_eq by (destruct (ksym K) as [[[b0 k0] n0]|]; [intros c0 e0 r0 []|exact I]).
apply chainKFF2_eqG; [exact HX|apply HX|reflexivity|reflexivity|].
intros sx _ HSK. unfold skipX in HSK. cbn [mk_sxi si_sx] in HSK.
destruct (match kbase K with Some _ => Pos.eqb (ef_bid ei) | None => fun _ => false end (sx_bid sx)) eqn:ES; [discriminate|].
match type of HSK with (if symnumJ ?a ?b then _ else _) = true => destruct (symnumJ a b) eqn:ESN end.
- exact (symnumJ_keep bc X sx K _ ESN).
- destruct (ksym K) as [[[b0 k0] n0]|] eqn:EKS; [|discriminate]. exact (sidesx_keep bc sx K b0 k0 n0 _ EKS HSK). }
cbn [in_grpo] in HG0. unfold in_grp in HG0. rewrite Hm in HG0. destruct HG0 as (obr0 & glo & ghi & EB & Hlo & Hhi).
rewrite (HE m eq_refl) in Hhi.
unfold mk_glF6. rewrite pt_get_map, EB.
destruct (pt_get (nt_info t) (ef_bid ei)) as [bi|] eqn:Hbi.
2:{ apply chainK2F2_eq; [exact HX|apply HX|reflexivity|exact I]. }
cbn [k_flo k_fl k_same].
assert (GM0 : forall gx, GMEMO bc glo ghi gx []) by (intros [x|]; [intros c e r []|exact I]).
rewrite (proj1 (mk_flM_eq bc (ef_bid ei) glo ghi _ _ sis [] (GM0 _))), (proj2 (mk_flM_eq bc (ef_bid ei) glo ghi _ _ sis [] (GM0 _))).
cbn [EINF ef_ei ei_kb ei_k ei_m ei_bid ei_br] in HK. destruct HK as (HD & HIn & Hbr). rewrite Hm in HD.
rewrite (nti_info _ _ _ _ HT HIn) in Hbi. injection Hbi as <-. cbn [bi_base bi_br]. rewrite Hbr.
set (obr := base_rangeB bc (ef_kb ei)).
set (gx := if is_litb (ef_kb ei) then None else Some (GXI (ef_kb ei) (xget X (ef_bid ei)))).
set (gqj := gqj_of (match obr with Some (lo2, hi2) => Some (glo + lo2, ghi + hi2) | None => None end)).
set (flo := if forallbF (fun e => if Pos.eqb (ef_bid ei) (sbe_b e) then true else hv_other (sbe_h e) gqj) sbl then []
else mk_flG (skipo5 bc (ef_bid ei) glo ghi gx gqj) sis).
change (match kbase K with Some _ => Pos.eqb (ef_bid ei) | None => fun _ => false end) with
(match kbase K with Some _ => Pos.eqb (ef_bid ei) | None => fun _ : positive => false end).
assert (PRG : forall K' sx, kbase K' = kbase K ->
prune1pcK bc (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) K'
(match kbase K with Some _ => Pos.eqb (ef_bid ei) | None => fun _ => false end (sx_bid sx))
(match kbase K with Some _ => obr | None => None end) = prG bc (ef_bid ei) (ef_kb ei) K' sx).
{ intros K' sx E. unfold prG. rewrite E. reflexivity. }
destruct flo as [|p0 fl0] eqn:EFLO.
2:{ apply chainKFF2_eqG; [exact HX|apply HX|reflexivity|exact I|]. intros sx Hsx HSK. rewrite (PRG K sx eq_refl).
exact (grp_keepV bc X t sxs HX HT HS (ef_bid ei) (ef_kb ei) glo ghi HIn K (ef_k ei) m sx HD Hlo Hhi Hsx HSK). }
assert (OTH : forall K' kk' m' sx, kbase K' = kbase K -> kdescr K' = Some (ef_kb ei, kk', Some m') -> glo <= kk' -> kk' + m' <= ghi ->
In sx sxs -> Pos.eqb (ef_bid ei) (sx_bid sx) = false ->
pk_rel K' PKeep (prune1pcK bc (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) K'
(match kbase K with Some _ => Pos.eqb (ef_bid ei) | None => fun _ => false end (sx_bid sx))
(match kbase K with Some _ => obr | None => None end))).
{ intros K' kk' m' sx EKB HD' Hlo' Hhi' Hsx Hne. left. symmetry. rewrite (PRG K' sx EKB).
exact (grp_oth bc X t sxs HX HT HS (ef_bid ei) (ef_kb ei) glo ghi HIn sbl K' kk' m' sx HSB1 HSB2 EFLO HD' Hlo' Hhi' Hsx Hne). }
assert (SAMEC : forall sx, In sx sxs -> Pos.eqb (ef_bid ei) (sx_bid sx) = true ->
match kbase K with Some _ => (match kbase K with Some _ => Pos.eqb (ef_bid ei) | None => fun _ => false end (sx_bid sx)) = true
| None => a_base (sx_a sx) = ELit 0 end).
{ intros sx Hsx ES. destruct (kdescr_kbase _ _ _ _ HD) as [HB|(lo & hi & -> & Hkb & Hk)].
- rewrite HB. exact ES.
- cbn [kbase]. pose proof (proj1 (Forall_forall _ _) HS sx Hsx) as (SXin & _ & _).
rewrite (nt_same_eq _ _ _ _ _ _ HT HIn SXin), Hkb in ES. apply p_expr_eqb_eq in ES. symmetry. exact ES. }
assert (FULL : forall se, In se sbl -> sbe_b se = ef_bid ei ->
chainKFF2 bc (xget X (ef_bid ei)) (sbe_fl se) K (kbase K)
(match kbase K with Some _ => Pos.eqb (ef_bid ei) | None => fun _ => false end)
(match kbase K with Some _ => obr | None => None end) None
= chainK2 bc sxs K (kbase K) (match kbase K with Some _ => Pos.eqb (ef_bid ei) | None => fun _ => false end)
(match kbase K with Some _ => obr | None => None end)).
{ intros se Hse Hseb. destruct (HSB1 se Hse) as [_ HFL]. rewrite Hseb in HFL. rewrite HFL.
apply chainKFF2_eqG2; [exact HX|apply HX|reflexivity|exact I|].
intros sx Hsx HSK. unfold osame in HSK. cbn [si_sx mk_sxi] in HSK.
destruct (Pos.eqb (ef_bid ei) (sx_bid sx)) eqn:ES; [discriminate|exact (OTH K _ _ sx eq_refl HD Hlo Hhi Hsx ES)]. }
destruct (sb_find sbl (ef_bid ei)) as [se|] eqn:ESB.
+ destruct (sb_find_in _ _ _ ESB) as [Hse Hseb]. destruct (HSB1 se Hse) as [HOK HFL]. unfold SBE_OK in HOK. rewrite Hseb in HOK, HFL.
destruct (hv_same (sbe_h se) (match z2b glo with Some a => match z2b ghi with Some e' => Some (a, e') | None => None end | None => None end)) eqn:EHS.
*
destruct (ent_iv K) as [[a e]|] eqn:EIV; [|exact (FULL se Hse Hseb)].
rewrite <- (chainKFF2_eqG2 bc X (xget X (ef_bid ei)) (fun _ => true) sxs K (kbase K) _ _ None HX (HX _) eq_refl I).
-- fold sis. rewrite mk_flG_all by reflexivity. reflexivity.
-- intros sx Hsx _. destruct (Pos.eqb (ef_bid ei) (sx_bid sx)) eqn:ES; [|exact (OTH K _ _ sx eq_refl HD Hlo Hhi Hsx ES)].
destruct (mk_flG_in (osame (ef_bid ei)) sis (mk_sxi X sx) (in_map _ _ _ Hsx)) as [r Hr].
{ unfold osame. cbn [si_sx mk_sxi]. rewrite ES. reflexivity. }
rewrite HOK in EHS. unfold hv_same in EHS.
destruct (hull_of (mk_flG (osame (ef_bid ei)) sis)) as [[[[A0 B0] c0] d0]|] eqn:EH; [|discriminate].
destruct (z2b glo) as [gl'|] eqn:EGL; [|discriminate]. destruct (z2b ghi) as [gh'|] eqn:EGH; [|discriminate].
destruct (hull_of_cov _ _ _ _ _ EH _ _ Hr) as (A & B & c & d & EA & EI & _ & _ & Lc & Ld).
destruct (ent_iv_descr _ _ _ _ _ _ EIV HD) as [Va Ve]. apply z2b_val in EGL. apply z2b_val in EGH.
apply (nonov_keep bc X sx K a e _ _ EIV); [|exact (SAMEC sx Hsx ES)].
apply (nonov_hull X sx a e gl' gh' c0 d0 A B c d EI EA Lc Ld); [apply ileb_true; lia|apply ileb_true; lia|exact EHS].
*
destruct (ent_iv K) as [[a e]|] eqn:EIV; [|exact (FULL se Hse Hseb)].
rewrite HFL. fold sis. destruct (ent_iv_descr _ _ _ _ _ _ EIV HD) as [Va Ve].
apply chainKP_eq; [exact HX|apply HX| |reflexivity|exact EIV].
intros K' a' e' EKB EI' La Le sx Hsx HSK. unfold osame in HSK. cbn [si_sx mk_sxi] in HSK.
destruct (Pos.eqb (ef_bid ei) (sx_bid sx)) eqn:ES.
-- apply (nonov_keep bc X sx K' a' e' _ _ EI' HSK). rewrite EKB. exact (SAMEC sx Hsx ES).
-- destruct (ent_iv_kdescr _ _ _ EI') as (kb' & kk' & m' & HD' & Va' & Ve').
assert (Ekb : kb' = ef_kb ei).
{ destruct (kdescr_kbase _ _ _ _ HD') as [HB'|(lo' & hi' & -> & Hkb' & _)];
destruct (kdescr_kbase _ _ _ _ HD) as [HB|(lo & hi & -> & Hkb & _)].
- rewrite HB', HB in EKB. injection EKB as ->. reflexivity.
- rewrite HB' in EKB. cbn [kbase] in EKB. discriminate.
- rewrite HB in EKB. cbn [kbase] in EKB. discriminate.
- congruence. }
subst kb'. apply (OTH K' kk' m' sx EKB HD'); [lia|lia|exact Hsx|exact ES].
+ rewrite <- (chainKFF2_eqG2 bc X (xget X (ef_bid ei)) (fun _ => true) sxs K (kbase K) _ _ None HX (HX _) eq_refl I).
* fold sis. rewrite mk_flG_all by reflexivity. reflexivity.
* intros sx Hsx _. apply (OTH K _ _ sx eq_refl HD Hlo Hhi Hsx). apply Pos.eqb_neq. intros Ebb.
destruct (HSB2 (mk_sxi X sx) (in_map _ _ _ Hsx)) as (se & Hse & Hseb). cbn [si_sx mk_sxi] in Hseb.
apply (sb_find_none _ _ ESB se Hse). rewrite Hseb. symmetry. exact Ebb.
- cbn [EINFF] in HK. cbn [option_map].
destruct (is_fact_entry K) eqn:HFK.
+ symmetry. apply chainK2_fact. exact HFK.
+ apply chainK2F2_eq; [exact HX|intros x Hx; discriminate|symmetry; apply kdescr_None_kbase; exact HK|exact I].
Qed.
Definition i16 : int := Uint63.of_Z 16.
Definition i4 : int := Uint63.of_Z 4.
Definition sgran (x : int) : int := PrimInt63.lsr x i4.
Fixpoint i2p (fuel : nat) (i : int) : positive :=
match fuel with
| O => xH
| S f => if PrimInt63.leb i i1 then xH
else if PrimInt63.eqb (PrimInt63.land i i1) i0 then xO (i2p f (PrimInt63.lsr i i1)) else xI (i2p f (PrimInt63.lsr i i1))
end.
Definition gkeyI (g : int) : positive := i2p 62 g.
Definition sfl : Type := list (sxi * list sxi).
Record ixb := IXB { ixb_b : positive; ixb_ok : bool; ixb_t : ptree sfl }.
Definition sbucket (t : ptree sfl) (k : positive) : sfl := match pt_get t k with Some l => l | None => [] end.
Fixpoint ix_find (l : list ixb) (b : positive) : option ixb :=
match l with [] => None | x :: r => if Pos.eqb b (ixb_b x) then Some x else ix_find r b end.
Fixpoint ix_upd (l : list ixb) (b : positive) (f : ixb -> ixb) : list ixb :=
match l with
| [] => [f (IXB b true PTLeaf)]
| x :: r => if Pos.eqb b (ixb_b x) then f x :: r else x :: ix_upd r b f
end.
Definition narrow (c d : int) : bool := if PrimInt63.ltb c d then PrimInt63.leb (PrimInt63.sub d c) i16 else false.
Definition ix_ins (p : sxi * list sxi) (c d : int) (x : ixb) : ixb :=
if narrow c d then
let k1 := gkeyI (sgran c) in
let k2 := gkeyI (sgran (PrimInt63.sub d i1)) in
let t1 := pt_set k1 (p :: sbucket (ixb_t x) k1) (ixb_t x) in
IXB (ixb_b x) (ixb_ok x) (if Pos.eqb k1 k2 then t1 else pt_set k2 (p :: sbucket t1 k2) t1)
else IXB (ixb_b x) false (ixb_t x).
Definition ix_add (l : list ixb) (si : sxi) (newer : list sxi) : list ixb :=
let b := sx_bid (si_sx si) in
match si_iv si with
| Some (c, d) => ix_upd l b (ix_ins (si, newer) c d)
| None => ix_upd l b (fun x => IXB (ixb_b x) false (ixb_t x))
end.
Definition ix_cands (l : list ixb) (b : positive) (a e : int) : option sfl :=
match ix_find l b with
| Some x =>
if ixb_ok x then
if PrimInt63.ltb a e then
let g := sgran a in
if PrimInt63.eqb g (sgran (PrimInt63.sub e i1)) then Some (sbucket (ixb_t x) (gkeyI g)) else None
else None
else None
| None => None
end.
Fixpoint sp9 (bc : bctx) (sbl : list sbe) (sis : list sxi) : list ixb * list kentry :=
match sis with
| [] => ([], [])
| si :: newer =>
let '(ixs, racc) := sp9 bc sbl newer in
let sx := si_sx si in
let b := sx_bid sx in
let K := KWord (sx_a sx) (sx_w sx) (sx_v sx) in
let gen := fun _ : unit => chainKFF2 bc (si_bx si) (mk_flG (skipS5 bc si) newer) K (Some (a_base (sx_a sx))) (Pos.eqb b) (sx_br sx) None in
let P := match si_iv si, si_eabj si with
| Some (a, e), Some (el, eh) =>
if forallbF (fun e' => if Pos.eqb b (sbe_b e') then true else hs_other (sbe_h e') el eh) sbl
then chainKI bc (si_bx si) (match ix_cands ixs b a e with Some fl => fl | None => mk_flG (osame b) newer end) a e K
(Some (a_base (sx_a sx))) (Pos.eqb b) (sx_br sx)
else gen tt
| _, _ => gen tt
end in
(ix_add ixs si newer, rev_append P racc)
end.
Definition stores_partF9 (bc : bctx) (sis : list sxi) (sbl : list sbe) : list kentry := rev' (snd (sp9 bc sbl sis)).
Definition notouch (G : int) (si : sxi) : Prop :=
exists c d, si_iv si = Some (c, d) /\ toZ c < toZ d /\ toZ d - toZ c <= 16 /\ G <> sgran c /\ G <> sgran (PrimInt63.sub d i1).
Inductive SubG (G : int) : sfl -> sfl -> Prop :=
| SubG_nil : SubG G [] []
| SubG_keep : forall x c f, SubG G c f -> SubG G (x :: c) (x :: f)
| SubG_drop : forall x c f, notouch G (fst x) -> SubG G c f -> SubG G c (x :: f).
Lemma SubG_refl : ltac2:(TCodec.tc2 tcn__FxCarry "8&Q2&Z8'U>r2r1%33211pl>51pRH71").
Proof. intros G l. induction l as [|x r IH]; [constructor|constructor; exact IH]. Qed.
Lemma i16_val : ltac2:(TCodec.tc2 tcn__FxCarry "7'G'N&Q8&W4%211+@%63521"). Proof. reflexivity. Qed.
Lemma i4_val : ltac2:(TCodec.tc2 tcn__FxCarry "7'G'N&Q8&W5%211+4%63521"). Proof. reflexivity. Qed.
Lemma sgran_val : ltac2:(TCodec.tc2 tcn__FxCarry ">&Q2'G'N&Q8&Z9r1%211%411&[D%614+@%3221%;3:51pQP0=1").
Proof. intros x. unfold sgran. rewrite Uint63Axioms.lsr_spec, i4_val. reflexivity. Qed.
Lemma iltb_ge : ltac2:(TCodec.tc2 tcn__FxCarry "B&Q2'G'8&Q5r2r1%3221(:%73621&[E&Q8%117r3%311%5231p071pQP4@1pQP0A1").
Proof.
intros x y H. destruct (Z.lt_ge_cases (toZ x) (toZ y)) as [L|G]; [|exact G].
apply Uint63Axioms.ltb_spec in L. congruence.
Qed.
Lemma notouch_nonov : ltac2:(TCodec.tc2 tcn__FxCarry "Q5&Q2'ZI&Y7r4r3%3221&[G&Q8%114r2%311%5231'G&Z9%11;r6%43@21&Q7&W3%22@1%711r7%:3F21'8&Y6r5%235;1(E%@3521p071p0>1p0D1p0K1piHQ11ph6Q21pnLQ21pRHQ41").
Proof.
intros G si a e (c & d & HI & Hcd & Hw & N1 & N2) Hae G1 G2. unfold nonov. rewrite HI.
destruct (PrimInt63.leb e c) eqn:E1; [reflexivity|]. apply ileb_gt in E1.
destruct (PrimInt63.leb d a) eqn:E2; [reflexivity|]. apply ileb_gt in E2. exfalso.
assert (Se : toZ (PrimInt63.sub e i1) = toZ e - 1) by (rewrite sub_nov; rewrite i1_val; [reflexivity|pose proof (Uint63.to_Z_bounded a); lia]).
assert (Sd : toZ (PrimInt63.sub d i1) = toZ d - 1) by (rewrite sub_nov; rewrite i1_val; [reflexivity|pose proof (Uint63.to_Z_bounded c); lia]).
assert (Ga : toZ a / 16 = toZ G) by (rewrite <- G1; symmetry; apply sgran_val).
assert (Ge : (toZ e - 1) / 16 = toZ G) by (rewrite <- Se, <- G2; symmetry; apply sgran_val).
assert (NC : toZ G <> toZ c / 16) by (intros E; apply N1; apply Uint63.to_Z_inj; rewrite sgran_val; exact E).
assert (ND : toZ G <> (toZ d - 1) / 16) by (intros E; apply N2; apply Uint63.to_Z_inj; rewrite sgran_val, Sd; exact E).
pose proof (Uint63.to_Z_bounded a). pose proof (Uint63.to_Z_bounded c).
set (x := Z.max (toZ a) (toZ c)).
assert (X1 : x / 16 = toZ G).
{ assert (toZ a / 16 <= x / 16) by (apply Z.div_le_mono; lia). assert (x / 16 <= (toZ e - 1) / 16) by (apply Z.div_le_mono; lia). lia. }
assert (X2 : x / 16 = toZ c / 16 \/ x / 16 = (toZ d - 1) / 16).
{ assert (toZ c / 16 <= x / 16) by (apply Z.div_le_mono; lia). assert (x / 16 <= (toZ d - 1) / 16) by (apply Z.div_le_mono; lia).
assert ((toZ d - 1) / 16 <= toZ c / 16 + 1).
{ replace (toZ c / 16 + 1) with ((toZ c + 1 * 16) / 16) by (rewrite Z.div_add by lia; reflexivity). apply Z.div_le_mono; lia. }
lia. }
destruct X2 as [X2|X2]; congruence.
Qed.
Lemma SubG_chainKI : ltac2:(TCodec.tc2 tcn__FxCarry "QO'RM'?'UH%211&Q2&Z8'QL'QJ%711'Q0'8p021'C'N%2211%>11'U>r9r8r7%43321&[G&Q8%114r6%311%5231'G&Z9%11;r;%43K21&Q7&W3%22@1%711r<%:3Q121'<%11Q1&V4r?r>r:r5%594392LKJE1%6954@3MLKF2%D3821p0;1p0B1p0H1p0O1phNQ51pnDQ:1pn0Q>1pRLQA1piHQD1ph6QE1pj0QE1pi>QF1pRHQH1pQP2QJ1phFQN1").
Proof.
intros bc xo G cands fl a e K okb same_of br2 HS Hae G1 G2. induction HS as [|[si rest] c f HS IH|[si rest] c f HN HS IH].
- reflexivity.
- cbn [chainKI]. rewrite IH. reflexivity.
- cbn [chainKI]. cbn [fst] in HN. rewrite (notouch_nonov G si a e HN Hae G1 G2). exact IH.
Qed.
Definition IXE_OK (newer : list sxi) (x : ixb) : Prop :=
ixb_ok x = true -> forall G, SubG G (sbucket (ixb_t x) (gkeyI G)) (mk_flG (osame (ixb_b x)) newer).
Definition IXL_OK (newer : list sxi) (l : list ixb) : Prop :=
(forall b x, ix_find l b = Some x -> ixb_b x = b /\ IXE_OK newer x) /\
(forall b, ix_find l b = None -> mk_flG (osame b) newer = []).
Lemma ix_find_upd_same : forall l b f, (forall x, ixb_b (f x) = ixb_b x) ->
ix_find (ix_upd l b f) b = Some (f (match ix_find l b with Some x => x | None => IXB b true PTLeaf end)).
Proof.
intros l b f Hf. induction l as [|y r IH]; cbn [ix_upd ix_find].
- rewrite Hf. cbn [ixb_b]. rewrite Pos.eqb_refl. reflexivity.
- destruct (Pos.eqb b (ixb_b y)) eqn:E; cbn [ix_find].
+ rewrite Hf, E. reflexivity.
+ rewrite E. exact IH.
Qed.
Lemma ix_find_upd_other : ltac2:(TCodec.tc2 tcn__FxCarry "Q3'<'WG%211'Q0pQP033'G&WHr2r1%211%411%513%73921pQP0<1&Ir3r4%<3>21%411'?%11C&WD&WFr6r5%3321:%521:%624;%G3821p0;1p0A1piNK1ph@M1ph>N1pl>Q01").
Proof.
intros l b b' f Hf NE. induction l as [|y r IH]; cbn [ix_upd ix_find].
- rewrite Hf. cbn [ixb_b]. destruct (Pos.eqb_spec b' b) as [E|_]; [exfalso; exact (NE E)|reflexivity].
- destruct (Pos.eqb b (ixb_b y)) eqn:E; cbn [ix_find].
+ rewrite Hf. apply Pos.eqb_eq in E. destruct (Pos.eqb_spec b' (ixb_b y)) as [E'|_]; [exfalso; apply NE; rewrite E', E; reflexivity|reflexivity].
+ rewrite IH. reflexivity.
Qed.
Lemma mk_flG_osame_same : ltac2:(TCodec.tc2 tcn__FxCarry "J'ZI'<%112'G'C%1253%511&X9&Y=&T?&Z<r2%211%411%611(9r1%23A61%;241(B%14DB94%>275%73A21%D3A51pmFF1pnLI1").
Proof. intros si newer. cbn [mk_flG]. unfold osame at 1. rewrite Pos.eqb_refl. reflexivity. Qed.
Lemma mk_flG_osame_other : ltac2:(TCodec.tc2 tcn__FxCarry "N'Q0'ZI'<%112&I'Gr3&T?&Z<r2%211%411%73<61%911'C%12><%>11&X9&Y=r4%211(9%13E@=%6231%724?%D3921p0=1pmFH1pnLK1ph>M1").
Proof.
intros b si newer NE. cbn [mk_flG]. unfold osame at 1. destruct (Pos.eqb_spec b (sx_bid (si_sx si))) as [E|_]; [exfalso; exact (NE E)|reflexivity].
Qed.
Lemma sbucket_set : forall (t : ptree sfl) k k' v, sbucket (pt_set k' v t) k = if Pos.eqb k k' then v else sbucket t k.
Proof.
intros t k k' v. unfold sbucket. destruct (Pos.eqb_spec k k') as [->|NE]; [rewrite pt_gss; reflexivity|rewrite (pt_gso _ _ _ _ _ NE); reflexivity].
Qed.
Lemma narrow_val : ltac2:(TCodec.tc2 tcn__FxCarry "I&Q2'G'8&Y3r2r1%3221(E%73621'F&[G&Q8r3%211%31:%5221&[E&[N%1245+@%4221%<261p0>1piDG1pi4H1").
Proof.
intros c d H. unfold narrow in H. destruct (PrimInt63.ltb c d) eqn:E; [|discriminate]. apply iltb_lt in E. apply ileb_le in H.
rewrite sub_nov, i16_val in H by lia. lia.
Qed.
Lemma IXE_ins : ltac2:(TCodec.tc2 tcn__FxCarry "R6'ZI'<%112&Q2'WG'G'?'C%1255%311&Z;r5%211(6(Br3r2%34>>21%52:1%>3:71'Q0&WH%116&T?&Z<r6%211%411%G3861'8&WI%11@(E%L3421'U>r1&Z4&WJ%11K&VH%115%5231&X9&Y=r9%E11%G11%411r8%7221%@3?91pRHQ@1p0C1&U1(9r7%23QH81&WE%Q<4QJQH:3r4%342Q3QA1%8251p0:1p0Q31p0Q=1pQP0QM1piDQO1pi4R01pmFR21pnLR51").
Proof.
intros si newer c d x HI Hb HX. unfold ix_ins. destruct (narrow c d) eqn:EN; [|intros H; discriminate H].
destruct (narrow_val _ _ EN) as [N1 N2].
intros Hok G. cbn [ixb_ok ixb_b ixb_t] in *. rewrite Hb, mk_flG_osame_same. specialize (HX Hok G).
set (k1 := gkeyI (sgran c)) in *. set (k2 := gkeyI (sgran (PrimInt63.sub d i1))) in *.
assert (DROP : gkeyI G <> k1 -> gkeyI G <> k2 -> notouch G si).
{ intros D1 D2. exists c, d. split; [exact HI|]. split; [exact N1|]. split; [exact N2|].
split; intros E; [apply D1|apply D2]; unfold k1, k2; rewrite E; reflexivity. }
destruct (Pos.eqb k1 k2) eqn:E12.
- apply Pos.eqb_eq in E12. rewrite sbucket_set. destruct (Pos.eqb_spec (gkeyI G) k1) as [E1|NE1].
+ apply SubG_keep. rewrite <- E1. exact HX.
+ apply SubG_drop; [cbn [fst]; apply DROP; [exact NE1|rewrite <- E12; exact NE1]|exact HX].
- apply Pos.eqb_neq in E12. rewrite sbucket_set. destruct (Pos.eqb_spec (gkeyI G) k2) as [E2|NE2].
+ rewrite sbucket_set. destruct (Pos.eqb_spec k2 k1) as [E|_]; [exfalso; apply E12; symmetry; exact E|]. apply SubG_keep. rewrite <- E2. exact HX.
+ rewrite sbucket_set. destruct (Pos.eqb_spec (gkeyI G) k1) as [E1|NE1].
* apply SubG_keep. rewrite <- E1. exact HX.
* apply SubG_drop; [cbn [fst]; apply DROP; assumption|exact HX].
Qed.
Lemma IXL_OK_add : ltac2:(TCodec.tc2 tcn__FxCarry "C'<'ZI%211'WG%411&U2r3r2%3221(9r4%23:41&WB%13763%9231p071pnL?1pl>=1pmF@1").
Proof.
intros newer l si [H1 H2]. set (b := sx_bid (si_sx si)).
assert (KEEP : forall f, (forall x, ixb_b (f x) = ixb_b x) ->
(forall x, ixb_b x = b -> (ixb_ok x = true -> forall G, SubG G (sbucket (ixb_t x) (gkeyI G)) (mk_flG (osame b) newer)) -> IXE_OK (si :: newer) (f x)) ->
IXL_OK (si :: newer) (ix_upd l b f)).
{ intros f Hf HF. split.
- intros b' x' HF'. destruct (Pos.eq_dec b' b) as [->|NE].
+ rewrite (ix_find_upd_same l b f Hf) in HF'. injection HF' as <-. rewrite Hf.
destruct (ix_find l b) as [x0|] eqn:E0.
* destruct (H1 b x0 E0) as [Hb0 HX0]. split; [exact Hb0|]. apply HF; [exact Hb0|]. intros Hok G. specialize (HX0 Hok G). rewrite Hb0 in HX0. exact HX0.
* split; [reflexivity|]. apply HF; [reflexivity|]. intros _ G. cbn [ixb_t]. unfold sbucket. rewrite pt_get_leaf, (H2 b E0). constructor.
+ rewrite (ix_find_upd_other l b b' f Hf NE) in HF'. destruct (H1 b' x' HF') as [Hb' HX']. split; [exact Hb'|].
intros Hok G. rewrite Hb', (mk_flG_osame_other b' si newer NE). specialize (HX' Hok G). rewrite Hb' in HX'. exact HX'.
- intros b' HN. destruct (Pos.eq_dec b' b) as [->|NE].
+ rewrite (ix_find_upd_same l b f Hf) in HN. discriminate HN.
+ rewrite (ix_find_upd_other l b b' f Hf NE) in HN. rewrite (mk_flG_osame_other b' si newer NE). exact (H2 b' HN). }
unfold ix_add. fold b. destruct (si_iv si) as [[c d]|] eqn:HI.
- apply KEEP.
+ intros x. unfold ix_ins. destruct (narrow c d); reflexivity.
+ intros x Hb HX. apply (IXE_ins si newer c d x HI Hb HX).
- apply KEEP; [intros x; reflexivity|]. intros x _ _ H. discriminate H.
Qed.
Definition sbkey (e : sbe) : positive * option hull := (sbe_b e, sbe_h e).
Lemma sb_pop_keys : ltac2:(TCodec.tc2 tcn__FxCarry "F'<'Z0%211'Q0'G'C'?&VO%211%4261%:11&M&Z3&YOr2r1%3221%64@851%74A964%?3921ph>A1pS4C1").
Proof. induction R as [|e r IH]; intros b; [reflexivity|]. cbn [sb_pop map]. rewrite IH. f_equal. destruct (Pos.eqb b (sbe_b e)); reflexivity. Qed.
Lemma forallbF_keys : ltac2:(TCodec.tc2 tcn__FxCarry "Q1'C'Q0'?&VO%211%5241'8p021'<'Z0%211'G%417&M&Z3r2%347;21r1%549=41%83731&VBr5%815%211qiH?1r3%63A21%73B3<%A3F21p0:1pfJD1pS4E1pj2I1").
Proof.
intros g R. induction R as [|e r IH]; intros S H; destruct S as [|e' s']; try discriminate; [reflexivity|].
cbn [map] in H. assert (H0 : sbkey e = sbkey e') by congruence. assert (Hr : map sbkey r = map sbkey s') by congruence.
cbn [forallbF]. rewrite H0, (IH s' Hr). reflexivity.
Qed.
Lemma forallbF_hs : forall b el eh R S, map sbkey R = map sbkey S ->
forallbF (fun e' => if Pos.eqb b (sbe_b e') then true else hs_other (sbe_h e') el eh) R
= forallbF (fun e' => if Pos.eqb b (sbe_b e') then true else hs_other (sbe_h e') el eh) S.
Proof. intros b el eh R S H. exact (forallbF_keys (fun p => if Pos.eqb b (fst p) then true else hs_other (snd p) el eh) R S H). Qed.
Lemma sb_find_some : ltac2:(TCodec.tc2 tcn__FxCarry "O'<'Z0%211'Q0'H'F&[>r1r3%33821'G&Z1%115r2%43;21%:261qiH?1%=2@1'?%11B&YNr4%221>(6%12GA%?3631qnJI1%G2J1p0;1ph>J1pS4L1").
Proof.
induction R as [|x r IH]; intros b (e & Hin & Hb); [destruct Hin|]. cbn [sb_find].
destruct (Pos.eqb_spec b (sbe_b x)) as [_|NE]; [eexists; reflexivity|].
destruct Hin as [<-|Hin]; [exfalso; apply NE; symmetry; exact Hb|]. apply IH. exists e. split; assumption.
Qed.
Lemma ix_cands_ok : ltac2:(TCodec.tc2 tcn__FxCarry "R0'<'ZI%211'WG%411'Q0&Q2&Z8&U2r6r5%3221'G'?%117&WCr4r3%349821(6r2%22>1%:3841'RM'UH%<11'QL'QJ%?11'8p0I1'C'N%2211%E11%Q319&V4r9r;r:r1%59Q0O432IHE1&X9&Y=r<%211r>%5221%<9Q7Q61:9Q0OL8%Q53>81phN@1pnDE1pn0H1pRLK1pQP2M1phFQ01p0Q21p0Q>1pj0QC1piHQE1ph6QF1ph>QH1pl>QJ1pmFQM1").
Proof.
intros newer l b a e fl [H1 _] HC bc xo K okb same_of br2. unfold ix_cands in HC.
destruct (ix_find l b) as [x|] eqn:EF; [|discriminate]. destruct (H1 b x EF) as [Hb HX].
destruct (ixb_ok x) eqn:Eok; [|discriminate]. destruct (PrimInt63.ltb a e) eqn:El; [|discriminate].
destruct (PrimInt63.eqb (sgran a) (sgran (PrimInt63.sub e i1))) eqn:Eg; [|discriminate]. injection HC as <-.
apply Uint63Axioms.eqb_correct in Eg. apply iltb_lt in El.
specialize (HX Eok (sgran a)). rewrite Hb in HX.
apply (SubG_chainKI bc xo (sgran a)); [exact HX|exact El|reflexivity|symmetry; exact Eg].
Qed.
Lemma sp9_eq : ltac2:(TCodec.tc2 tcn__FxCarry "R7'RM'<'ZI%211'Z0%411&U=r4r2r1%43321&[>%13:35'H'Fr5%53<71'G'Q0&Z1%11;&T?&Z<r3%211%411%93861%=2;1qiHH1%@2I1p0B1pnLM1'C'?&VO%211%42B1%Q411&M&Z3%24Q441A%34Q552J%I3521&U2&;'WG%Q=11'QL%Q?11&ZBr8r6%3321Q5%93751%;2Q71&[@&D%13;95%32;1&ZF%13:Q=QE%Q<3=31%Q@281p0E1p0Q11p0QG1pS4QM1pnNR01pnFQO1ph<R21phFR61").
Proof.
intros bc all sbl sis. induction sis as [|si newer IH]; intros R HR HC HK.
- cbn [sp9 fst snd stores_partF5 rev]. split; [|reflexivity]. split; [intros b x H; discriminate H|intros b _; reflexivity].
- cbn [sp9 stores_partF5]. cbv zeta.
set (b := sx_bid (si_sx si)).
assert (HR' : SBL_OK all newer (sb_pop R b)) by (apply sb_pop_ok; exact HR).
assert (HC' : forall si', In si' newer -> exists e, In e (sb_pop R b) /\ sbe_b e = sx_bid (si_sx si')).
{ intros si' Hsi. destruct (HC si' (or_intror Hsi)) as (e0 & He0 & Hb0).
destruct (sb_pop_bases R b e0 He0) as (e & E1 & E2 & _). exists e. split; [exact E1|congruence]. }
assert (HK' : map sbkey (sb_pop R b) = map sbkey sbl) by (rewrite sb_pop_keys; exact HK).
destruct (IH _ HR' HC' HK') as [HIX HREV].
destruct (sp9 bc sbl newer) as [ixs racc] eqn:ESP. cbn [fst snd] in *.
split; [apply IXL_OK_add; exact HIX|].
rewrite rev_append_rev, rev_app_distr, rev_involutive, HREV. f_equal.
destruct (si_iv si) as [[a e]|] eqn:EIV; [|reflexivity].
destruct (si_eabj si) as [[el eh]|] eqn:EE; [|reflexivity].
rewrite (forallbF_hs b el eh (sb_pop R b) sbl HK').
destruct (forallbF _ sbl); [|reflexivity].
destruct (sb_find_some (sb_pop R b) b) as [se ESB].
{ destruct (HC si (or_introl eq_refl)) as (e0 & He0 & Hb0). destruct (sb_pop_bases R b e0 He0) as (e1 & E1 & E2 & _).
exists e1. split; [exact E1|]. rewrite E2. exact Hb0. }
rewrite ESB. destruct (sb_find_in _ _ _ ESB) as [Hse Hseb]. destruct (HR' se Hse) as [_ HFL]. rewrite HFL, Hseb.
destruct (ix_cands ixs b a e) as [fl|] eqn:EC; [|reflexivity].
apply (ix_cands_ok newer ixs b a e fl HIX EC).
Qed.
Lemma stores_partF9_eq : ltac2:(TCodec.tc2 tcn__FxCarry "Q>'RM'<'ZI%211'Z0%411&U=r3r2r1%43321&[>r4%23;41'H'Fr5%63=81'G'Q0&Z1%11<&T?&Z<%11A%311%83751%<2:1qiHH1%?2I1p0A1pnLM1'QL%Q011&ZGr6%231HM&ZF%133JO%E3631p091p0O1pnFQ51pnNQ81ph<Q91phFQ=1").
Proof.
intros bc all sis sbl H1 H2. unfold stores_partF9, rev'. rewrite <- rev_alt. exact (proj2 (sp9_eq bc all sbl sis sbl H1 H2 eq_refl)).
Qed.
Definition long_log (sis : list sxi) : bool := match skipn 512 sis with [] => false | _ :: _ => true end.
Definition stores_partX (bc : bctx) (sis : list sxi) (sbl : list sbe) : list kentry :=
if long_log sis then stores_partF9 bc sis sbl else stores_partF5 bc sis sbl.
Lemma stores_partX_eq : ltac2:(TCodec.tc2 tcn__FxCarry "Q>'RM'<'ZI%211'Z0%411&U=r3r2r1%43321&[>r4%23;41'H'Fr5%63=81'G'Q0&Z1%11<&T?&Z<%11A%311%83751%<2:1qiHH1%?2I1p0A1pnLM1'QL%Q011&ZHr6%231HM&ZF%133JO%E3631p091p0O1pnFQ51pnNQ81ph<Q91phFQ=1").
Proof. intros bc all sis sbl H1 H2. unfold stores_partX. destruct (long_log sis); [exact (stores_partF9_eq bc all sis sbl H1 H2)|reflexivity]. Qed.
Definition carryGF8C (bc : bctx) (log : list sentry) (scs : list sprep) (kn : list kentry) : list kentry :=
let '(sxs, t0) := mk_stxsC2 log scs nt_empty in
let '(r, gs) := scanF2 bc kn t0 gst_empty None None in
let '(infos, t1) := r in
let sbs := store_bases sxs PTLeaf in
let X := pt_map (fun bi => if existsbF (fun sb => shares_var sb (bi_base bi)) sbs then Some (mk_bx bc (bi_base bi)) else None) (nt_info t1) in
let sis := map (mk_sxi X) sxs in
let sbl := mk_sbl sis sis [] in
stores_partF5 bc sis sbl ++ entriesGF8 bc X sis (mk_glF6 bc (nt_info t1) X (gs_bnds gs) sis sbl) kn infos.
Lemma carryGF8_eq : ltac2:(TCodec.tc2 tcn__FxCarry "I'RM'<'R6%211'QL%411'G&UKr3r2&M'R<&XC&X6%116%3271%64>517r1%;4:921&S0%13<;3%?3@31pl8A1plLD1phFH1").
Proof.
intros bc log kn. unfold carryGF8C, carryG. rewrite mk_stxsC2_eq.
destruct (mk_stxs bc log nt_empty) as [sxs t0] eqn:E0.
destruct (mk_stxs_okG _ _ _ _ _ (NTI_empty bc) E0) as (HT0 & HS0 & _).
rewrite (scanF2_eq bc kn t0 gst_empty None None HT0 I I).
destruct (scanF bc kn t0 gst_empty) as [[infos t1] gs] eqn:ES.
destruct (scan_entries bc kn t0 gst_empty) as [[infos' t1'] gs'] eqn:ES'.
destruct (scanF_sim _ _ _ _ _ _ _ _ _ _ _ ES ES') as [<- HI].
destruct (scanF_okG _ _ _ _ _ _ _ HT0 ES) as (HT1 & Hm & HF).
destruct (scan_entries_okG _ _ _ _ _ _ _ HT0 ES') as (_ & _ & HF').
destruct (scanF_grp _ _ _ _ _ _ _ GSI_empty ES) as (_ & _ & HGR).
assert (HS1 : Forall (SX_OK bc t1) sxs).
{ apply Forall_impl with (P := SX_OK bc t0); [|exact HS0]. intros sx. apply SX_OK_mono. exact Hm. }
cbv zeta.
match goal with |- context [mk_sbl ?s ?s []] => destruct (mk_sbl_ok s s [] (fun e (H : In e []) => match H with end)) as (HSB1 & HSB2 & _) end.
rewrite (stores_partF5_eq bc _ t0 _ sxs _ (XOK_map _ _ _) HS0 HSB1 HSB2 (fun si H => H)). f_equal.
rewrite (entriesGF8_C bc _ t1 sxs gs kn infos); [|apply XOK_map|exact HT1|exact HS1|exact HF|exact HGR].
rewrite (entriesG_C bc t1 sxs _ kn infos' HT1 HS1 HF'). apply entC_strip. exact HI.
Qed.
Fixpoint mk_stxsR (log : list sentry) (scs : list sprep) (t : ntab) : list stx * ntab :=
match log, scs with
| SE a w v :: older, sp :: scs' =>
let '(rs, t1) := mk_stxsR older scs' t in
let '(r, t2) := intern_r t1 (a_base a) (sp_rng sp) in
let '(bid, bi) := r in
(STX a w v sp bid (bi_br bi) :: rs, t2)
| _, _ => ([], t)
end.
Definition mk_stxsC3 (log : list sentry) (scs : list sprep) (t : ntab) : list stx * ntab :=
let '(rs, t') := mk_stxsR log scs t in (rev' rs, t').
Lemma mk_stxsR_eq : ltac2:(TCodec.tc2 tcn__FxCarry "N'<'R6%211'R<%411'T1'G'C'T;%911%3215&XMr3r2r1%43321(B&[@&;&XJ%13876%33<@1%52>1&D%13?C4%94@D31%D3@;1po<F1pnHH1plLK1").
Proof.
induction log as [|[a w v] older IH]; intros scs t; [reflexivity|]. destruct scs as [|sp scs']; [reflexivity|].
cbn [mk_stxsR mk_stxsC2]. rewrite IH. destruct (mk_stxsC2 older scs' t) as [sxs t1]. cbn [fst snd].
destruct (intern_r t1 (a_base a) (sp_rng sp)) as [[bid bi] t2]. cbn [fst snd]. rewrite rev_app_distr. reflexivity.
Qed.
Lemma mk_stxsC3_eq : ltac2:(TCodec.tc2 tcn__FxCarry "F'<'R6%211'R<%411'T1'G'C'T;%911%3215&XKr3r2r1%43321&XJ%13543%<3831po<>1pnH@1plLC1").
Proof.
intros log scs t. unfold mk_stxsC3. rewrite mk_stxsR_eq. destruct (mk_stxsC2 log scs t) as [sxs t1]. cbn [fst snd].
unfold rev'. rewrite <- rev_alt, rev_involutive. reflexivity.
Qed.
Definition carryGF9C (bc : bctx) (log : list sentry) (scs : list sprep) (kn : list kentry) : list kentry :=
let '(sxs, t0) := mk_stxsC3 log scs nt_empty in
let '(r, gs) := scanF2 bc kn t0 gst_empty None None in
let '(infos, t1) := r in
let sbs := store_bases sxs PTLeaf in
let X := pt_map (fun bi => if existsbF (fun sb => shares_var sb (bi_base bi)) sbs then Some (mk_bx bc (bi_base bi)) else None) (nt_info t1) in
let sis := map (mk_sxi X) sxs in
let sbl := mk_sbl sis sis [] in
stores_partX bc sis sbl ++ entriesGF8 bc X sis (mk_glF6 bc (nt_info t1) X (gs_bnds gs) sis sbl) kn infos.
Lemma carryGF9C_eq8 : ltac2:(TCodec.tc2 tcn__FxCarry "F'RM'<'R6%211'R<%411'QL%611'G&ULr4r3r2r1%544321&UK%146543%93:31pl8;1pnH>1plLA1phFE1").
Proof.
intros bc log scs kn. unfold carryGF9C, carryGF8C. rewrite mk_stxsC3_eq.
destruct (mk_stxsC2 log scs nt_empty) as [sxs t0]. destruct (scanF2 bc kn t0 gst_empty None None) as [[infos t1] gs]. cbv zeta.
match goal with |- context [mk_sbl ?s ?s []] => destruct (mk_sbl_ok s s [] (fun e (H : In e []) => match H with end)) as (HSB1 & HSB2 & _);
rewrite (stores_partX_eq bc s s (mk_sbl s s []) HSB1 HSB2) end.
reflexivity.
Qed.
Definition carryKF (bc : bctx) (log : list sentry) (kn : list kentry) (hints : list bool)
: list kentry * list sidecond * list bool :=
match log, hints with
| [], _ => (kn, [], hints)
| _, [] => (carryGF9C bc log (map (mk_sctx bc (mk_bext bc)) log) kn, [], [])
| _, _ => carryB bc log kn hints
end.
Definition carryKF_ctx (bc : bctx) (log : list sentry) (scs : list sprep) (kn : list kentry) (hints : list bool)
: list kentry * list sidecond * list bool :=
match log, hints with
| [], _ => (kn, [], hints)
| _, [] => (carryGF9C bc log scs kn, [], [])
| _, _ => carryB bc log kn hints
end.
Lemma carryKF_eq : ltac2:(TCodec.tc2 tcn__FxCarry "E'G'RM'<'R6%211'QL%411'8%611'C'R7%911%3261%4215pk261pl891plL<1phF@1&UM&S1%D3321").
Proof.
fe. rename x into bc, x0 into log, x1 into kn, x2 into hints. unfold carryKF, carryK.
destruct log as [|s older]; [reflexivity|]. destruct hints; [|reflexivity]. rewrite carryGF9C_eq8, carryGF8_eq. reflexivity.
Qed.
Lemma carryKF_ctx_eq : ltac2:(TCodec.tc2 tcn__FxCarry "Q2'RM'<'R6%211'QL%411'8%611'G'C'R7%:11%3271%4216&UOr4r3&M'R<&XC&X6%116%3271%64E517r2r1%<5;:321&UM%14=<43%E3@31pk2G1pl8J1plLM1phFQ11").
Proof. intros bc log kn hints. unfold carryKF_ctx, carryKF. destruct log; [reflexivity|]. destruct hints; reflexivity. Qed.
Definition omax (a b : option Z) : option Z :=
match a, b with Some x, Some y => Some (Z.max x y) | Some x, None => Some x | None, o => o end.
Definition oshift (o : option Z) (d : Z) : option Z := match o with Some l => Some (l + d) | None => None end.
Definition ok_lo (o : option Z) (c : Z) : bool := match o with Some l => Z.leb 0 (l + c) | None => false end.
Definition lin_lo (bc : bctx) (ts : list (Z * expr)) : option Z :=
let la := match lin_range (erangeB bc) 0 ts with Some (lo, _) => Some lo | None => None end in
let lb := match bc_fs bc with
| [] => None
| fs => match sum_subst fs ts 0 0 false with
| (ts', (lo0, hi0), true) =>
match lin_range (erangeB bc) 0 ts' with Some (lo, _) => Some (lo + lo0) | None => None end
| _ => None
end
end in
omax la lb.
Lemma ok_lo_omax : ltac2:(TCodec.tc2 tcn__FxCarry "D'?'N%211'G'8&Y;&Y<r3r2%3221r1%6221&A%8263%9264%3221%=3<51pi4@1ph>@1ph6A1").
Proof.
intros [x|] [y|] c; cbn [omax ok_lo]; rewrite ?Bool.orb_false_r; try reflexivity.
destruct (Z.leb_spec 0 (x + c)), (Z.leb_spec 0 (y + c)), (Z.leb_spec 0 (Z.max x y + c)); cbn [orb]; try reflexivity; lia.
Qed.
Lemma ok_lo_oshift : ltac2:(TCodec.tc2 tcn__FxCarry "C'?'N%211'G'8&Y;&Y>r3r2%3221r1%6221&[C%1235%9271%<3;41pi4?1piD@1pmL@1").
Proof. intros [l|] d c; cbn [oshift ok_lo]; [|reflexivity]. f_equal. ring. Qed.
Lemma lin_testB_lo : ltac2:(TCodec.tc2 tcn__FxCarry "K'RM'N'<'C'QJ%2241%411'G'8&SJr3r2r1&[Fz%2214q0?1qlH@1%948761&Y;&X1%12;9%321;%@3?51poDB1pi4H1phFJ1").
Proof.
intros bc c ts. unfold lin_testB, lin_test_relB, lin_lo. rewrite ok_lo_omax.
rewrite (lin_range_shift _ c ts).
destruct (bc_fs bc) as [|f fs].
- destruct (lin_range (erangeB bc) 0 ts) as [[lo hi]|]; cbn [ok_lo]; rewrite ?Bool.orb_false_r; [|reflexivity].
destruct (Z.leb 0 (lo + c)); reflexivity.
- destruct (sum_subst (f :: fs) ts 0 0 false) as [[ts' [lo0 hi0]] [|]].
+ rewrite (lin_range_shift _ c ts').
destruct (lin_range (erangeB bc) 0 ts) as [[lo hi]|]; destruct (lin_range (erangeB bc) 0 ts') as [[lo' hi']|]; cbn [ok_lo orb];
rewrite ?Bool.orb_false_r; try reflexivity.
* replace (lo' + c + lo0) with (lo' + lo0 + c) by ring. destruct (Z.leb 0 (lo + c)); reflexivity.
* destruct (Z.leb 0 (lo + c)); reflexivity.
* f_equal. ring.
+ destruct (lin_range (erangeB bc) 0 ts) as [[lo hi]|]; cbn [ok_lo]; rewrite ?Bool.orb_false_r; [|reflexivity].
destruct (Z.leb 0 (lo + c)); reflexivity.
Qed.
Record gp := GP { gp_u : option Z; gp_s : option (Z * Z) }.
Definition mk_gp (bc : bctx) (ts : list (Z * expr)) : gp :=
let l1 := lin_lo bc ts in
let '(c2, t2) := srl_expandB bc ts in
let l2 := oshift (lin_lo bc t2) c2 in
let l3 := if has_srl t2 then let '(c3, t3) := srl_expandB bc t2 in oshift (lin_lo bc t3) (c2 + c3) else None in
let j := srl_scale_need ts in
GP (omax l1 (omax l2 l3))
(if (if Z.ltb 0 j then Z.leb j 24 else false) then
let sc := 2 ^ j in
let ts' := List.map (fun t => (sc * fst t, snd t)) ts in
let '(c2', t2') := srl_expandB bc ts' in
let '(c3', t3') := (if has_srl t2' then srl_expandB bc t2' else (0, t2')) in
match lin_lo bc t3' with Some l => Some (sc, l + c2' + c3') | None => None end
else None).
Definition ge0P (g : gp) (C : Z) : bool :=
if ok_lo (gp_u g) C then true else match gp_s g with Some (sc, l) => Z.leb 0 (l + sc * C) | None => false end.
Lemma lin_ge0_scaledB_gp : forall bc C ts, lin_ge0_scaledB bc C ts = match gp_s (mk_gp bc ts) with Some (sc, l) => Z.leb 0 (l + sc * C) | None => false end.
Proof.
intros bc C ts. unfold lin_ge0_scaledB, mk_gp.
destruct (srl_expandB bc ts) as [c2 t2]. cbn [gp_s].
destruct (if Z.ltb 0 (srl_scale_need ts) then Z.leb (srl_scale_need ts) 24 else false); [|reflexivity].
cbv zeta.
destruct (srl_expandB bc (List.map (fun t => (2 ^ srl_scale_need ts * fst t, snd t)) ts)) as [c2' t2'].
destruct (if has_srl t2' then srl_expandB bc t2' else (0, t2')) as [c3' t3'].
rewrite lin_testB_lo. destruct (lin_lo bc t3') as [l|]; cbn [ok_lo]; [|reflexivity]. f_equal. ring.
Qed.
Lemma lin_ge0B_gp : ltac2:(TCodec.tc2 tcn__FxCarry "Q1'RM&RA'G'8&SGr3r2r1%43321&7&TI%1265%2275%4221&VE&X=&R1&R@%11<%21<%4221%62@1&[N&R?%11B%21B%4221%=261%C2?1%K3JE1pmBM1pn4N1phFQ01").
Proof.
intros bc pos neg. unfold lin_ge0B. f_equal.
set (ts := lsub_e (xt_lin pos) (xt_lin neg)). set (C := xt_const pos - xt_const neg).
unfold ge0P. rewrite <- lin_ge0_scaledB_gp. unfold mk_gp.
destruct (srl_expandB bc ts) as [c2 t2] eqn:E2. cbn [gp_u].
rewrite !ok_lo_omax, !lin_testB_lo.
destruct (ok_lo (lin_lo bc ts) C); [reflexivity|]. cbn [orb].
rewrite ok_lo_oshift. destruct (ok_lo (lin_lo bc t2) (C + c2)); [reflexivity|]. cbn [orb].
destruct (has_srl t2).
- destruct (srl_expandB bc t2) as [c3 t3]. rewrite lin_testB_lo, ok_lo_oshift.
replace (C + (c2 + c3)) with (C + c2 + c3) by ring. destruct (ok_lo (lin_lo bc t3) (C + c2 + c3)); reflexivity.
- reflexivity.
Qed.
Inductive xin :=
| XNo
| XLin (gA : gp) (a1 a2 : Z) (gB : gp) (b2 : Z)
| XNum (a lo1 hi1 b : Z).
Record binf := BINF { bi_l1 : Z; bi_nw : bool; bi_x1 : list (Z * expr); bi_rng : option (Z * Z) }.
Definition mk_binf (bc : bctx) (b1 : expr) : binf :=
BINF (fst (lin_of b1)) (lin_nowrapRB bc b1) (xt_lin [(b1, 0)]) (base_rangeB bc b1).
Definition gp_dead (g : gp) : bool := match g with GP None None => true | _ => false end.
Definition mk_xin (bc : bctx) (b1 : expr) (bi : binf) (cb : expr) (co : Z) (m : expr) : xin :=
if shares_var b1 cb then
if bi_nw bi then
if lin_nowrapRB bc cb then
let gA := mk_gp bc (lsub_e (bi_x1 bi) (xt_lin [(cb, co)])) in
if gp_dead gA then XNo else
if lin_nowrapRB bc m then
XLin gA (bi_l1 bi) (fst (lin_of cb) + co + 0) (mk_gp bc (lsub_e (xt_lin [(cb, co); (m, 0)]) (bi_x1 bi)))
(fst (lin_of cb) + co + (fst (lin_of m) + 0 + 0))
else XNo
else XNo
else XNo
else if novars cb then
match xloB bc cb, xhiB bc cb with
| Some lo2, Some hi2 =>
if Z.eqb lo2 hi2 then
match bi_rng bi, xloB bc m with
| Some (lo1, hi1), Some l2 => XNum (lo2 + co) lo1 hi1 (lo2 + co + l2)
| _, _ => XNo
end
else XNo
| _, _ => XNo
end
else XNo.
Definition xeval (x : xin) (k sn zn : Z) (nwn : bool) : bool :=
match x with
| XNo => false
| XLin gA a1 a2 gB b2 =>
if ge0P gA (a1 + k + 0 - a2) then (if nwn then ge0P gB (b2 - (a1 + k + (sn + 0 + 0))) else false) else false
| XNum a lo1 hi1 b => if Z.leb a (lo1 + k) then Z.leb (hi1 + k + zn) b else false
end.
Lemma gp_dead_false : ltac2:(TCodec.tc2 tcn__FxCarry "A'VJ'N'G'8&VKr2%211(E%63521&VEr3%2216(:%;3:21p061p:>1pj2@1").
Proof. intros [[u|] [s|]] C H; try discriminate. reflexivity. Qed.
Lemma xeval_eq : ltac2:(TCodec.tc2 tcn__FxCarry "Q4'RM'QJ'N'G'8&[5&Y1r7r6&X7%1232r5r4r3%86764321r2&R8r1%211&RB%113&SI(QB%116%32A1%D5;:751&TG%17DC<4@?>%I3H31pm8K1pkFL1plNN1piBN1pi@Q01phBQ11phFQ31").
Proof.
intros bc b1 cb co m k n. unfold mk_xin, xinsideB. cbn [bi_l1 bi_nw bi_x1 bi_rng mk_binf].
destruct (shares_var b1 cb).
- unfold xinside0B. rewrite !lin_ge0B_gp. cbn [xt_nowrapB xt_const].
change (xt_lin [(b1, k)]) with (xt_lin [(b1, 0)]).
change (xt_lin [(b1, k); (ELit n, 0)]) with (xt_lin [(b1, 0)]).
change (fst (lin_of (ELit n))) with (snorm n).
destruct (lin_nowrapRB bc b1); [|reflexivity]. destruct (lin_nowrapRB bc cb); [|reflexivity]. cbn [andb].
destruct (gp_dead (mk_gp bc (lsub_e (xt_lin [(b1, 0)]) (xt_lin [(cb, co)])))) eqn:ED.
{ rewrite (gp_dead_false _ _ ED). reflexivity. }
destruct (lin_nowrapRB bc m); cbn [xeval andb].
+ destruct (ge0P _ (fst (lin_of b1) + k + 0 - (fst (lin_of cb) + co + 0))); [|reflexivity].
destruct (lin_nowrapRB bc (ELit n)); reflexivity.
+ destruct (ge0P _ (fst (lin_of b1) + k + 0 - (fst (lin_of cb) + co + 0))); reflexivity.
- destruct (novars cb); [|reflexivity]. unfold xinside_numB.
destruct (xloB bc cb) as [lo2|]; [|reflexivity]. destruct (xhiB bc cb) as [hi2|]; [|reflexivity].
destruct (Z.eqb lo2 hi2); [|reflexivity].
destruct (base_rangeB bc b1) as [[lo1 hi1]|]; [|reflexivity]. cbn [xhiB].
destruct (xloB bc m) as [l2|]; [|reflexivity]. cbn [xeval].
destruct (Z.leb (lo2 + co) (lo1 + k)); reflexivity.
Qed.
Record sidet := SDT { sd_off : Z; sd_xlo : option Z; sd_x : xin }.
Definition mk_sidet (bc : bctx) (b1 : expr) (bi : binf) (c : saddr) (m : expr) : sidet :=
SDT (a_off c) (if expr_eqbF b1 (a_base c) then xloB bc m else None) (mk_xin bc b1 bi (a_base c) (a_off c) m).
Definition num_subW (s : sidet) (k n : Z) : bool :=
match sd_xlo s with
| Some ml => if Z.leb (sd_off s) k then Z.leb (k + n) (sd_off s + ml) else false
| None => false
end.
Definition sd_dead (s : sidet) : bool := match sd_xlo s, sd_x s with None, XNo => true | _, _ => false end.
Inductive wrow := WR (c1 : saddr) (m1 : expr) (s1 : sidet) (c2 : saddr) (m2 : expr) (s2 : sidet).
Fixpoint mk_rows (bc : bctx) (b1 : expr) (bi : binf) (kd : list kentry) : list wrow :=
match kd with
| [] => []
| KDisj c1 m1 c2 m2 :: rest =>
let s1 := mk_sidet bc b1 bi c1 m1 in
let s2 := mk_sidet bc b1 bi c2 m2 in
if (if sd_dead s1 then sd_dead s2 else false) then mk_rows bc b1 bi rest
else WR c1 m1 s1 c2 m2 s2 :: mk_rows bc b1 bi rest
| _ :: rest => mk_rows bc b1 bi rest
end.
Fixpoint disj_bothW (rows : list wrow) (k n sn zn : Z) (nwn : bool) : list (saddr * expr) * list (saddr * expr) :=
match rows with
| [] => ([], [])
| WR c1 m1 s1 c2 m2 s2 :: rest =>
let '(r, rx) := disj_bothW rest k n sn zn nwn in
let x2 := xeval (sd_x s2) k sn zn nwn in
let x1 := xeval (sd_x s1) k sn zn nwn in
let r1 := if (if num_subW s2 k n then true else x2) then (c1, m1) :: r else r in
let rx1 := if x2 then (c1, m1) :: rx else rx in
((if (if num_subW s1 k n then true else x1) then (c2, m2) :: r1 else r1),
(if x1 then (c2, m2) :: rx1 else rx1))
end.
Lemma num_subW_eq : ltac2:(TCodec.tc2 tcn__FxCarry "K'RM'QJ'R5'N'G'8&Y:&XGr6r5&X7%1232r4r3%7565321r2r1%;3321&Y9%16;:4376%@3?31pm8B1pkFC1plNF1pi4F1phBH1phFJ1").
Proof.
intros bc b1 c m k n. unfold num_subW, num_sub, mk_sidet. cbn [sd_off sd_xlo].
eF.
destruct (expr_eqb b1 (a_base c)); [|reflexivity].
destruct (xloB bc m) as [ml|]; [|destruct (Z.leb (a_off c) k); reflexivity].
destruct (Z.leb (a_off c) k); reflexivity.
Qed.
Lemma sd_dead_false : ltac2:(TCodec.tc2 tcn__FxCarry "Q:'RM'QJ'R5'N'G'8&Z7&XGr6r5&X7%1232r4r3%7565321%911(E%=3<21'F&Y9r7r2%362>91=:(:%D3C21&TG(QB%116&QG%11D&QH%11F%77<HC531D%M3L1:%@2:1p0B1pm8Q11pkFQ21plNQ51pi4Q51phBQ71phFQ91").
Proof.
intros bc b1 c m k n H. rewrite <- num_subW_eq, <- xeval_eq. unfold sd_dead, num_subW in *.
cbn [sd_xlo sd_x mk_sidet] in *. eF.
destruct (if expr_eqb b1 (a_base c) then xloB bc m else None); [discriminate|].
destruct (mk_xin bc b1 (mk_binf bc b1) (a_base c) (a_off c) m); try discriminate. split; reflexivity.
Qed.
Lemma disj_bothW_eq : ltac2:(TCodec.tc2 tcn__FxCarry "Q7'RM'QJ'<'QL%211'N'G'C'R5%2218%811%4211&V8&X@r5r4&X7%1232r3%645421r2r1&R8%112&RB%114&SI(QB%117%32?1%B6;:9751&V7%15B>A<;%K3F31pm8M1pkFN1pl2Q01phBQ41phFQ61").
Proof.
intros bc b1 kd k n. induction kd as [|K rest IH]; [reflexivity|].
destruct K as [a w' v|a len|a len bk|lo hi|e' m'|e' lo' hi'|a en|c1 m1 c2 m2|a len fc|a len]; cbn [mk_rows disj_both]; try exact IH.
destruct (if sd_dead (mk_sidet bc b1 (mk_binf bc b1) c1 m1) then sd_dead (mk_sidet bc b1 (mk_binf bc b1) c2 m2) else false) eqn:ED.
- destruct (sd_dead (mk_sidet bc b1 (mk_binf bc b1) c1 m1)) eqn:E1; [|discriminate].
destruct (sd_dead_false bc b1 c1 m1 k n E1) as [N1 X1]. destruct (sd_dead_false bc b1 c2 m2 k n ED) as [N2 X2].
rewrite IH, N1, N2, X1, X2. destruct (disj_both bc rest b1 k n) as [r rx]. reflexivity.
- cbn [disj_bothW]. rewrite IH. destruct (disj_both bc rest b1 k n) as [r rx].
rewrite !num_subW_eq. cbn [sd_x mk_sidet]. rewrite !xeval_eq. reflexivity.
Qed.
Record wtab := WT { wt_rng : option (Z * Z); wt_rows : list wrow }.
Definition mk_wtab (bc : bctx) (kd : list kentry) (b1 : expr) : wtab :=
let bi := mk_binf bc b1 in WT (bi_rng bi) (mk_rows bc b1 bi kd).
Definition mk_sctxW (bc : bctx) (kd : list kentry) (t : wtab) (a : saddr) (w : nat) : sprep :=
let n := Z.of_nat w in
if (if Z.leb 0 n then Z.ltb n two63z else false) then
let '(D, Dx) := disj_bothW (wt_rows t) (a_off a) n n n true in SPrep (wt_rng t) (Some n) D Dx
else mk_sprepF bc kd (a_base a) (a_off a) (elen w).
Lemma mk_sctxW_eq : ltac2:(TCodec.tc2 tcn__FxCarry "M'RM'<'QL%211'R5'='G'R<&XDr4r3&XO&QGr2%211%43651r1%9587241&XI&QH%117&QI%116%55>=931%B3A71poJD1ph6F1pl2H1phFL1").
Proof.
intros bc kd a w. unfold mk_sctxW. cbv zeta.
destruct (if Z.leb 0 (Z.of_nat w) then Z.ltb (Z.of_nat w) two63z else false) eqn:EN; [|reflexivity].
assert (Hn : 0 <= Z.of_nat w < two63z).
{ destruct (Z.leb_spec 0 (Z.of_nat w)); [|discriminate]. destruct (Z.ltb_spec (Z.of_nat w) two63z); [lia|discriminate]. }
assert (Hz : zlit64 (Z.of_nat w) = Z.of_nat w).
{ unfold zlit64. rewrite two63z_val in Hn. destruct (Z.leb_spec 0 (Z.of_nat w)), (Z.ltb_spec (Z.of_nat w) two64); cbn [andb]; try reflexivity; rewrite two64_val in *; lia. }
assert (Hs : snorm (Z.of_nat w) = Z.of_nat w) by (apply snorm_small; rewrite mtwo63z_val; rewrite two63z_val in *; lia).
pose proof (disj_bothW_eq bc (a_base a) kd (a_off a) (Z.of_nat w)) as HD.
rewrite Hs, Hz, (lin_nowrapRB_lit bc _ Hn) in HD.
unfold mk_wtab. cbn [wt_rows wt_rng]. rewrite HD.
unfold mk_sprepF, elen. rewrite Hz, Z.eqb_refl. cbn [bi_rng mk_binf xhiB]. rewrite Hz. reflexivity.
Qed.
Definition wtabs : Type := list (expr * wtab).
Definition wt_empty : wtabs := [].
Fixpoint wc_find (c : wtabs) (b : expr) : option wtab :=
match c with [] => None | (b', t) :: r => if expr_eqbF b b' then Some t else wc_find r b end.
Definition mk_sctx_c1 (bc : bctx) (ex : bext) (c : wtabs) (s : sentry) : sprep * wtabs :=
match s with
| SE a w v =>
match wc_find c (a_base a) with
| Some t => (mk_sctxW bc (be_kd ex) t a w, c)
| None => let t := mk_wtab bc (be_kd ex) (a_base a) in (mk_sctxW bc (be_kd ex) t a w, (a_base a, t) :: c)
end
end.
Definition WTOK (bc : bctx) (ex : bext) (c : wtabs) : Prop := forall b t, In (b, t) c -> t = mk_wtab bc (be_kd ex) b.
Lemma WTOK_empty : ltac2:(TCodec.tc2 tcn__FxCarry "9'RM'UD&U@r2r1&[2%43321piL61phF81").
Proof. intros bc ex b t []. Qed.
Lemma wc_find_ok : ltac2:(TCodec.tc2 tcn__FxCarry "Q1'RM'UD&[4'QJ'[3&U@r5r4r3%43321'G'?%118&ZN%1276(6r2%22=1%83641&XOr7&UCr6%211%5341A%?3EA1p081p0B1po<H1ph>J1pi4L1piLN1phFQ01").
Proof.
intros bc ex c b t. induction c as [|[b' t'] r IH]; intros H HF; [discriminate|]. cbn [wc_find] in HF. eF.
destruct (expr_eqb b b') eqn:E.
- injection HF as <-. apply p_expr_eqb_eq in E. subst b'. apply H. left. reflexivity.
- apply IH; [intros b0 t0 Hin; apply H; right; exact Hin|exact HF].
Qed.
Lemma mk_sctx_c1_fst : ltac2:(TCodec.tc2 tcn__FxCarry "H'RM'UD&[4'R6&U@r4r3r2%43321'G'R<&;&XFr5%241987%435=1&XC%134<:%93831p0;1pn@A1pi4C1piLE1phFG1").
Proof.
intros bc ex c [a w v] H. unfold mk_sctx_c1, mk_sctx.
destruct (wc_find c (a_base a)) as [t|] eqn:EF; cbn [fst].
- rewrite (wc_find_ok bc ex c _ t H EF). apply mk_sctxW_eq.
- apply mk_sctxW_eq.
Qed.
Lemma mk_sctx_c1_ok : ltac2:(TCodec.tc2 tcn__FxCarry "E'RM'UD&[4'R6&U@r4r3r2%43321r5&D'R<&XF%144876%433<1%;36:1p081pn@>1pi4@1piLB1phFD1").
Proof.
intros bc ex c [a w v] H. unfold mk_sctx_c1.
destruct (wc_find c (a_base a)) as [t|] eqn:EF; cbn [snd]; [exact H|].
intros b t [E|Hin]; [injection E as <- <-; reflexivity|exact (H b t Hin)].
Qed.
Definition rmemo : Type := list (expr * option (Z * Z)).
Fixpoint rm_find (M : rmemo) (a : expr) : option (option (Z * Z)) :=
match M with [] => None | (a', r) :: rest => if expr_eqbF a a' then Some r else rm_find rest a end.
Definition rm_get (bc : bctx) (M : rmemo) (a : expr) : option (Z * Z) * rmemo :=
match rm_find M a with Some r => (r, M) | None => let r := erangeB bc a in (r, (a, r) :: M) end.
Definition MOK (bc : bctx) (M : rmemo) : Prop := forall a r, In (a, r) M -> r = erangeB bc a.
Lemma rm_find_ok : ltac2:(TCodec.tc2 tcn__FxCarry "N'RM&YL'QJ'?'C'N%2211%411&U7r4r3%3221'G%:16&YJ%1265(6r2%22;1%73641&S9r6%221=%;3@=1p051p0>1pn<C1ph6I1pS0K1phFM1").
Proof.
intros bc M a r. induction M as [|[a' r'] rest IH]; intros H HF; [discriminate|]. cbn [rm_find] in HF. eF.
destruct (expr_eqb a a') eqn:E.
- injection HF as <-. apply p_expr_eqb_eq in E. subst a'. apply H. left. reflexivity.
- apply IH; [intros a0 r0 H0; apply H; right; exact H0|exact HF].
Qed.
Lemma rm_get_ok : ltac2:(TCodec.tc2 tcn__FxCarry "N'RM&YL'QJ&U7r3r2%3221'F'G'?'C'N%2211%411&;&YKr4%231=<%435A1&S9%124?%=3831&D%13:F6%E281%B241p0D1ph6I1pS0K1phFM1").
Proof.
intros bc M a H. unfold rm_get. destruct (rm_find M a) as [r|] eqn:E; cbn [fst snd].
- split; [exact (rm_find_ok bc M a r H E)|exact H].
- split; [reflexivity|]. intros a0 r0 [E0|H0]; [injection E0 as <- <-; reflexivity|exact (H a0 r0 H0)].
Qed.
Fixpoint lin_rangeM (bc : bctx) (M : rmemo) (c : Z) (ts : list (Z * expr)) : option (Z * Z) * rmemo :=
match ts with
| [] => (Some (c, c), M)
| (k, a) :: rest =>
let '(ra, M1) := rm_get bc M a in
match ra with
| Some (al, ah) =>
let '(rr, M2) := lin_rangeM bc M1 c rest in
(match rr with
| Some (lo, hi) => if Z.leb 0 k then Some (lo + k * al, hi + k * ah) else Some (lo + k * ah, hi + k * al)
| None => None
end, M2)
| None => (None, M1)
end
end.
Lemma lin_rangeM_ok : ltac2:(TCodec.tc2 tcn__FxCarry "Q6'RM'N'<'C'QJ%2241%411&YL&U7r4r1%3221'F'G'?%<2>>%211&;&X3r5r2r3%4432=1%637@1&R0&S9%117%331B6%?3<51&D%13>G8%G2<1%D241p0F1pS0K1poDM1pi4Q31phFQ51").
Proof.
intros bc c ts. induction ts as [|[k a] rest IH]; intros M H; [split; [reflexivity|exact H]|].
cbn [lin_rangeM lin_range]. destruct (rm_get_ok bc M a H) as [E1 H1]. destruct (rm_get bc M a) as [ra M1]. cbn [fst snd] in E1, H1.
rewrite <- E1. destruct ra as [[al ah]|]; [|split; [reflexivity|exact H1]].
destruct (IH M1 H1) as [E2 H2]. destruct (lin_rangeM bc M1 c rest) as [rr M2]. cbn [fst snd] in *. rewrite <- E2.
split; [|exact H2]. destruct rr as [[lo hi]|]; reflexivity.
Qed.
Definition lin_loM (bc : bctx) (M : rmemo) (ts : list (Z * expr)) : option Z * rmemo :=
let '(ra, M1) := lin_rangeM bc M 0 ts in
let la := match ra with Some (lo, _) => Some lo | None => None end in
match bc_fs bc with
| [] => (omax la None, M1)
| fs => match sum_subst fs ts 0 0 false with
| (ts', (lo0, hi0), true) =>
let '(rb, M2) := lin_rangeM bc M1 0 ts' in
(omax la (match rb with Some (lo, _) => Some (lo + lo0) | None => None end), M2)
| _ => (omax la None, M1)
end
end.
Lemma lin_loM_ok : ltac2:(TCodec.tc2 tcn__FxCarry "Q1'RM'<'C'N'QJ%3221%511&YL&U7r3r1%3221'F'G'?%11<&;&X2r4r2%3321;%536>1&X1%125>%;3931&D%13;C6%C291%@241p0B1pS0G1poDI1phFQ01").
Proof.
intros bc ts M H. unfold lin_loM, lin_lo.
destruct (lin_rangeM_ok bc 0 ts M H) as [E1 H1]. destruct (lin_rangeM bc M 0 ts) as [ra M1]. cbn [fst snd] in E1, H1. rewrite <- E1.
destruct (bc_fs bc) as [|f fs]; [split; [reflexivity|exact H1]|].
destruct (sum_subst (f :: fs) ts 0 0 false) as [[ts' [lo0 hi0]] [|]]; [|split; [reflexivity|exact H1]].
destruct (lin_rangeM_ok bc 0 ts' M1 H1) as [E2 H2]. destruct (lin_rangeM bc M1 0 ts') as [rb M2]. cbn [fst snd] in *. rewrite <- E2.
split; [reflexivity|exact H2].
Qed.
Definition mk_gpM (bc : bctx) (M : rmemo) (ts : list (Z * expr)) : gp * rmemo :=
let '(l1, M1) := lin_loM bc M ts in
let '(c2, t2) := srl_expandB bc ts in
let '(l2r, M2) := lin_loM bc M1 t2 in
let l2 := oshift l2r c2 in
let '(l3, M3) := if has_srl t2 then let '(c3, t3) := srl_expandB bc t2 in let '(l3r, M3) := lin_loM bc M2 t3 in (oshift l3r (c2 + c3), M3)
else (None, M2) in
let j := srl_scale_need ts in
if (if Z.ltb 0 j then Z.leb j 24 else false) then
let sc := 2 ^ j in
let ts' := List.map (fun t => (sc * fst t, snd t)) ts in
let '(c2', t2') := srl_expandB bc ts' in
let '(c3', t3') := (if has_srl t2' then srl_expandB bc t2' else (0, t2')) in
let '(l4, M4) := lin_loM bc M3 t3' in
(GP (omax l1 (omax l2 l3)) (match l4 with Some l => Some (sc, l + c2' + c3') | None => None end), M4)
else (GP (omax l1 (omax l2 l3)) None, M3).
Lemma mk_gpM_ok : ltac2:(TCodec.tc2 tcn__FxCarry "Q0'RM'<'C'N'QJ%3221%511&YL&U7r3r1%3221'F'G'VJ&;&X>r4r2%3321:%536=1&X=%125=%:3931&D%13;B6%B291%?241p0A1pS0F1poDH1phFO1").
Proof.
intros bc ts M H. unfold mk_gpM, mk_gp.
destruct (lin_loM_ok bc ts M H) as [E1 H1]. destruct (lin_loM bc M ts) as [l1 M1]. cbn [fst snd] in E1, H1. rewrite <- E1.
destruct (srl_expandB bc ts) as [c2 t2].
destruct (lin_loM_ok bc t2 M1 H1) as [E2 H2]. destruct (lin_loM bc M1 t2) as [l2r M2]. cbn [fst snd] in E2, H2. rewrite <- E2.
assert (S3 : exists l3 M3, (if has_srl t2 then let '(c3, t3) := srl_expandB bc t2 in let '(l3r, M3) := lin_loM bc M2 t3 in (oshift l3r (c2 + c3), M3) else (None, M2)) = (l3, M3)
/\ l3 = (if has_srl t2 then let '(c3, t3) := srl_expandB bc t2 in oshift (lin_lo bc t3) (c2 + c3) else None) /\ MOK bc M3).
{ destruct (has_srl t2); [|exists None, M2; split; [reflexivity|split; [reflexivity|exact H2]]].
destruct (srl_expandB bc t2) as [c3 t3]. destruct (lin_loM_ok bc t3 M2 H2) as [E3 H3]. destruct (lin_loM bc M2 t3) as [l3r M3]. cbn [fst snd] in E3, H3.
exists (oshift l3r (c2 + c3)), M3. split; [reflexivity|]. split; [rewrite E3; reflexivity|exact H3]. }
destruct S3 as (l3 & M3 & -> & -> & H3). cbv zeta.
destruct (if Z.ltb 0 (srl_scale_need ts) then Z.leb (srl_scale_need ts) 24 else false); [|split; [reflexivity|exact H3]].
destruct (srl_expandB bc (List.map (fun t => (2 ^ srl_scale_need ts * fst t, snd t)) ts)) as [c2' t2'].
destruct (if has_srl t2' then srl_expandB bc t2' else (0, t2')) as [c3' t3'].
destruct (lin_loM_ok bc t3' M3 H3) as [E4 H4]. destruct (lin_loM bc M3 t3') as [l4 M4]. cbn [fst snd] in *. rewrite <- E4.
split; [reflexivity|exact H4].
Qed.
Definition nmemo : Type := list (expr * bool).
Fixpoint nm_find (N : nmemo) (e : expr) : option bool :=
match N with [] => None | (e', r) :: rest => if expr_eqbF e e' then Some r else nm_find rest e end.
Definition nm_get (bc : bctx) (N : nmemo) (e : expr) : bool * nmemo :=
match nm_find N e with Some r => (r, N) | None => let r := lin_nowrapRB bc e in (r, (e, r) :: N) end.
Definition NOK (bc : bctx) (N : nmemo) : Prop := forall e r, In (e, r) N -> r = lin_nowrapRB bc e.
Lemma nm_get_ok : ltac2:(TCodec.tc2 tcn__FxCarry "J'RM&Y5'QJ&U8r3r2%3221'F'G'8&;&Y4r4%23198%435=1&SI%124;%93831&D%13:B6%A281%>241p0@1piHE1pS2G1phFI1").
Proof.
intros bc N e H. unfold nm_get.
assert (F : forall r, nm_find N e = Some r -> r = lin_nowrapRB bc e).
{ clear - H. induction N as [|[e' r'] rest IH]; intros r HF; [discriminate|]. cbn [nm_find] in HF. eF.
destruct (expr_eqb e e') eqn:E.
- injection HF as <-. apply p_expr_eqb_eq in E. subst e'. apply H. left. reflexivity.
- apply IH; [intros e0 r0 H0; apply H; right; exact H0|exact HF]. }
destruct (nm_find N e) as [r|]; cbn [fst snd].
- split; [exact (F r eq_refl)|exact H].
- split; [reflexivity|]. intros e0 r0 [E0|H0]; [injection E0 as <- <-; reflexivity|exact (H e0 r0 H0)].
Qed.
Definition bmemo : Type := (rmemo * nmemo)%type.
Definition BOK (bc : bctx) (B : bmemo) : Prop := MOK bc (fst B) /\ NOK bc (snd B).
Definition mk_xinM (bc : bctx) (B : bmemo) (b1 : expr) (bi : binf) (cb : expr) (co : Z) (m : expr) : xin * bmemo :=
if shares_var b1 cb then
if bi_nw bi then
let '(nwc, N1) := nm_get bc (snd B) cb in
if nwc then
let '(gA, M1) := mk_gpM bc (fst B) (lsub_e (bi_x1 bi) (xt_lin [(cb, co)])) in
if gp_dead gA then (XNo, (M1, N1)) else
let '(nwm, N2) := nm_get bc N1 m in
if nwm then
let '(gB, M2) := mk_gpM bc M1 (lsub_e (xt_lin [(cb, co); (m, 0)]) (bi_x1 bi)) in
(XLin gA (bi_l1 bi) (fst (lin_of cb) + co + 0) gB (fst (lin_of cb) + co + (fst (lin_of m) + 0 + 0)), (M2, N2))
else (XNo, (M1, N2))
else (XNo, (fst B, N1))
else (XNo, B)
else (mk_xin bc b1 bi cb co m, B).
Lemma mk_xinM_ok : ltac2:(TCodec.tc2 tcn__FxCarry "Q5'RM'QJ'UE'N&UF&TKr7r1%3221'F'G'[7&;&Y2r8r2r6r5r4r3%7765>4321%93:A1&Y1%169A7654%>3=31&D%13?F6%F2=1%C241p0E1p6J1plNN1piBM1pi@Q01phHQ01phBQ21phFQ41").
Proof.
intros bc b1 bi cb co m [M N] [HM HN]. unfold mk_xinM. cbn [fst snd]. destruct (shares_var b1 cb) eqn:ES; [|split; [reflexivity|split; assumption]].
unfold mk_xin. rewrite ES.
destruct (bi_nw bi); [|split; [reflexivity|split; assumption]].
destruct (nm_get_ok bc N cb HN) as [EN1 HN1]. destruct (nm_get bc N cb) as [nwc N1]. cbn [fst snd] in EN1, HN1. rewrite <- EN1.
destruct nwc; [|split; [reflexivity|split; assumption]].
destruct (mk_gpM_ok bc (lsub_e (bi_x1 bi) (xt_lin [(cb, co)])) M HM) as [E1 H1].
destruct (mk_gpM bc M (lsub_e (bi_x1 bi) (xt_lin [(cb, co)]))) as [gA M1]. cbn [fst snd] in E1, H1. rewrite <- E1.
destruct (gp_dead gA); [split; [reflexivity|split; assumption]|].
destruct (nm_get_ok bc N1 m HN1) as [EN2 HN2]. destruct (nm_get bc N1 m) as [nwm N2]. cbn [fst snd] in EN2, HN2. rewrite <- EN2.
destruct nwm; [|split; [reflexivity|split; assumption]].
destruct (mk_gpM_ok bc (lsub_e (xt_lin [(cb, co); (m, 0)]) (bi_x1 bi)) M1 H1) as [E2 H2].
destruct (mk_gpM bc M1 (lsub_e (xt_lin [(cb, co); (m, 0)]) (bi_x1 bi))) as [gB M2]. cbn [fst snd] in *. rewrite <- E2.
split; [reflexivity|split; assumption].
Qed.
Definition mk_sidetM (bc : bctx) (B : bmemo) (b1 : expr) (bi : binf) (c : saddr) (m : expr) : sidet * bmemo :=
let '(x, B1) := mk_xinM bc B b1 bi (a_base c) (a_off c) m in
(SDT (a_off c) (if expr_eqbF b1 (a_base c) then xloB bc m else None) x, B1).
Lemma mk_sidetM_ok : ltac2:(TCodec.tc2 tcn__FxCarry "Q3'RM'QJ'UE'R5&UF&TKr6r1%3221'F'G'Z=&;&XHr7r2r5r4r3%6654=321%839@1&XG%158@654%=3<31&D%13>E6%E2<1%B241p0D1p6I1plNM1pi4L1phHN1phBQ01phFQ21").
Proof.
intros bc b1 bi c m B H. unfold mk_sidetM, mk_sidet. destruct (mk_xinM_ok bc b1 bi (a_base c) (a_off c) m B H) as [E1 H1].
destruct (mk_xinM bc B b1 bi (a_base c) (a_off c) m) as [x B1]. cbn [fst snd] in *. rewrite <- E1. split; [reflexivity|exact H1].
Qed.
Fixpoint mk_rowsM (bc : bctx) (B : bmemo) (b1 : expr) (bi : binf) (kd : list kentry) : list wrow * bmemo :=
match kd with
| [] => ([], B)
| KDisj c1 m1 c2 m2 :: rest =>
let '(s1, B1) := mk_sidetM bc B b1 bi c1 m1 in
let '(s2, B2) := mk_sidetM bc B1 b1 bi c2 m2 in
let '(rows, B3) := mk_rowsM bc B2 b1 bi rest in
((if (if sd_dead s1 then sd_dead s2 else false) then rows else WR c1 m1 s1 c2 m2 s2 :: rows), B3)
| _ :: rest => mk_rowsM bc B b1 bi rest
end.
Lemma mk_rowsM_ok : ltac2:(TCodec.tc2 tcn__FxCarry "Q4'RM'QJ'UE'<'QL%211&UF&TKr5r1%3221'F'G'[1%;11&;&XAr6r2r4r3%5543=21%738@1&X@%147@54%=3;31&D%13=E6%E2;1%B241p0D1p6I1pl2K1phHO1phBQ11phFQ31").
Proof.
intros bc b1 bi kd. induction kd as [|K rest IH]; intros B H; [split; [reflexivity|exact H]|].
destruct K as [a w' v|a len|a len bk|lo hi|e' m'|e' lo' hi'|a en|c1 m1 c2 m2|a len fc|a len]; cbn [mk_rowsM mk_rows]; try exact (IH B H).
destruct (mk_sidetM_ok bc b1 bi c1 m1 B H) as [E1 H1]. destruct (mk_sidetM bc B b1 bi c1 m1) as [s1 B1]. cbn [fst snd] in E1, H1.
destruct (mk_sidetM_ok bc b1 bi c2 m2 B1 H1) as [E2 H2]. destruct (mk_sidetM bc B1 b1 bi c2 m2) as [s2 B2]. cbn [fst snd] in E2, H2.
destruct (IH B2 H2) as [E3 H3]. destruct (mk_rowsM bc B2 b1 bi rest) as [rows B3]. cbn [fst snd] in *.
rewrite <- E1, <- E2, <- E3. split; [|exact H3]. destruct (if sd_dead s1 then sd_dead s2 else false); reflexivity.
Qed.
Definition mk_wtabM (bc : bctx) (B : bmemo) (kd : list kentry) (b1 : expr) : wtab * bmemo :=
let bi := mk_binf bc b1 in
let '(rows, B1) := mk_rowsM bc B b1 bi kd in (WT (bi_rng bi) rows, B1).
Lemma mk_wtabM_ok : ltac2:(TCodec.tc2 tcn__FxCarry "Q0'RM'<'QL%211'QJ&UF&TKr4r1%3221'F'G'[3&;&Y0r5r2r3%4432;1%637>1&XO%136>4%;3:31&D%13<C6%C2:1%@241p0B1p6G1phBI1pl2K1phFO1").
Proof.
intros bc kd b1 B H. unfold mk_wtabM, mk_wtab. destruct (mk_rowsM_ok bc b1 (mk_binf bc b1) kd B H) as [E1 H1].
destruct (mk_rowsM bc B b1 (mk_binf bc b1) kd) as [rows B1]. cbn [fst snd] in *. rewrite <- E1. split; [reflexivity|exact H1].
Qed.
Definition wcache : Type := (bmemo * list (expr * wtab))%type.
Definition wc_empty : wcache := (([], []), []).
Definition mk_sctx_c (bc : bctx) (ex : bext) (c : wcache) (s : sentry) : sprep * wcache :=
match s with
| SE a w v =>
match wc_find (snd c) (a_base a) with
| Some t => (mk_sctxW bc (be_kd ex) t a w, c)
| None => let '(t, B') := mk_wtabM bc (fst c) (be_kd ex) (a_base a) in (mk_sctxW bc (be_kd ex) t a w, (B', (a_base a, t) :: snd c))
end
end.
Definition WCOK (bc : bctx) (ex : bext) (c : wcache) : Prop := BOK bc (fst c) /\ WTOK bc ex (snd c).
Lemma WCOK_empty : ltac2:(TCodec.tc2 tcn__FxCarry "9'RM'UD&U?r2r1&ZM%43321piL61phF81").
Proof. intros bc ex. split; [split; [intros a r []|intros e r []]|apply WTOK_empty]. Qed.
Lemma mk_sctx_c_fst : ltac2:(TCodec.tc2 tcn__FxCarry "H'RM'UD&ZO'R6&U?r4r3r2%43321'G'R<&;&XEr5%241987%435=1&XC%134<:%93831p0;1pn@A1pi4C1piLE1phFG1").
Proof.
intros bc ex [B c] [a w v] [HB HC]. unfold mk_sctx_c, mk_sctx. cbn [fst snd].
destruct (wc_find c (a_base a)) as [t|] eqn:EF; cbn [fst].
- rewrite (wc_find_ok bc ex c _ t HC EF). apply mk_sctxW_eq.
- destruct (mk_wtabM_ok bc (be_kd ex) (a_base a) B HB) as [E1 _]. destruct (mk_wtabM bc B (be_kd ex) (a_base a)) as [t B']. cbn [fst] in *.
rewrite E1. apply mk_sctxW_eq.
Qed.
Lemma mk_sctx_c_ok : ltac2:(TCodec.tc2 tcn__FxCarry "E'RM'UD&ZO'R6&U?r4r3r2%43321r5&D'R<&XE%144876%433<1%;36:1p081pn@>1pi4@1piLB1phFD1").
Proof.
intros bc ex [B c] [a w v] [HB HC]. unfold mk_sctx_c. cbn [fst snd].
destruct (wc_find c (a_base a)) as [t|] eqn:EF; cbn [snd]; [split; assumption|].
destruct (mk_wtabM_ok bc (be_kd ex) (a_base a) B HB) as [E1 H1]. destruct (mk_wtabM bc B (be_kd ex) (a_base a)) as [t B']. cbn [fst snd] in *.
split; [exact H1|]. intros b t0 [E|Hin]; [injection E as <- <-; exact E1|exact (HC b t0 Hin)].
Qed.
End CARF.
