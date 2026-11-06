(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg DivergeSim SpinAlg AgentLib AsanAcct AsanAcctShape AsanPlacement BackingAlgebra.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import AxSymExec3K AxSymExec3SoundK AxSymRun3K AsanPlanK.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__AsanPlanSoundK () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Nat."; "Corelib.Init.Peano."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.Fs."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Instr."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanAcct."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanPlanK.APK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanPlanSoundK.APSK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanPlanSoundK.APSK.Sound."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanPlanSoundK.APSK.Sound.Rename."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanPlanSoundK.APSK.Sound.RenameCS."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AxSymExec3K.AX2K."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AxSymExec3SoundK.AX2SK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AxSymRun3K."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.DivergeSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ShapeAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StoreOk."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0A"; "1None"; "1O"; "1S"; "1Some"; "1andb"; "1app"; "1bool"; "1cons"; "1false"; "1fst"; "1length"; "1list"; "1nat"; "1negb"; "1nil"]; ["1option"; "1pair"; "1prod"; "1snd"; "1true"; "2False"; "2True"; "2and"; "2eq"; "2ex"; "2iff"; "2not"; "2or"; "3add"; "4le"; "4lt"]; ["5Forall"; "5map"; "5nth"; "6Z"; "0D"; "0E"; "0E'"; "0E1"; "0E2"; "0E3"; "0FULL"; "0FULL'"; "0H"; "0H1"; "0H2"; "0HOLES"]; ["0HS"; "0IT"; "0J"; "0K"; "0KC"; "0LIMIT"; "7Fs"; "8fetch_word"; "8machine_state"; "8ms_pc"; "8ms_svc_pending"; "8wview"; "9Model"; "9event"; "9m_fs"; "9m_vm_lazy"]; ["9m_vmmaps"; "9map_remove"; "9page_base"; "9page_in_ranges"; "9vm_limit"; ":M_MUL"; ":aluop"; ":mulop"; ";bvmap"; "0M"; "0M'"; "0M0"; "0N"; "0P"; "0R"; "0R'"]; ["<A_bytes"; "<A_wf"; "<H_off_segments"; "<MInv"; "<eager_used"; "<lazy_cover"; "<mrestrict"; "<munrestrict"; "<page_allowedb"; "<same_but_materialized"; "=ACS"; "=AM"; "=COk"; "=SPIN_WORD"; "=a_brk"; "=a_fd"]; ["=a_ghost"; "=a_hlz"; "=a_hna"; "=a_maps"; "=a_ss"; "=a_vis"; "=acs"; "=add_kn"; "=afd"; "=afd_eqb"; "=am_base"; "=am_len"; "=amap"; "=amap_eqb"; "=asubst"; "=check"]; ["=check_all"; "=cover1"; "=cover_x"; "=cres"; "=cs_gc"; "=csvars_all"; "=cutout1"; "=cutout1p"; "=deand"; "=disj_side_fact"; "=disj_var_fact"; "=drop_ixs"; "=e_sp0"; "=e_sppg"; "=entails"; "=entails_h"]; ["=erename"; "=esubst"; "=evars_all"; "=expr_vars_lt"; "=fact_ok"; "=fd_vars_lt"; "=find_disj"; "=flat_x"; "=fog_token"; "=fresh_ok"; "=fsubst"; "=havoc1"; "=havoc1p"; "=hist_vars_lt"; "=hole_only"; "=hop"]; ["=hop_b"; "=hop_eqb"; "=hop_n"; "=hop_sub"; "=hrename"; "=hsubst"; "=hw_apply"; "=hw_go"; "=hw_val"; "=inst"; "=is_fog"; "=is_hole"; "=is_tok_kind"; "=kdisj_shadow_twin"; "=kentry_apart_b"; "=kentry_apart_bp"]; ["=kentry_eqb"; "=kentry_eqb_h"; "=kentry_vars_lt"; "=kfind_litword"; "=kflat_h"; "=kimg_clip"; "=kimg_cut"; "=kn"; "=kn_bigsubst"; "=kn_contra"; "=kn_cutout"; "=kn_havoc"; "=kn_incl_h"; "=kn_vars_lt"; "=krename"; "=ksubst"]; ["=kunk_covered"; "=kvars_all"; "=kwr_cut"; "=kzero_x"; "=listZ_eqb"; "=list_insert_nth"; "=list_set_nth"; "=lit_of"; "=loop_ok"; "=loopctx"; "=maps_vars_lt"; "=mk_bwd"; "=mk_fwd"; "=mk_itab_ranges"; "=mk_itab_ranges_acc"; "=mkind"]; ["=mkind_eqb"; "=mrename"; "=msubst"; "=no_fog"; "=node_abstractcell"; "=node_absword"; "=node_bump"; "=node_casedisj"; "=node_compact"; "=node_diamond_join"; "=node_droprange"; "=node_fog"; "=node_fognew"; "=node_ghost"; "=node_habs"; "=node_havoc"]; ["=node_havocbig"; "=node_havocbrk"; "=node_havocwords"; "=node_intro"; "=node_rename"; "=node_respell"; "=node_shdisj"; "=node_unvis"; "=nt_get"; "=nxt"; "=pair_eqb"; "=pairs_vars_lt"; "=pc"; "=plan"; "=reg"; "=reg_lit"]; ["=regs_match_h"; "=rename_cs"; "=residue_fact"; "=respell_ok"; "=run_block"; "=run_block_gc"; "=salt2"; "=scaled_var"; "=set_kn"; "=set_regs"; "=shadow_of"; "=shadow_off"; "=shape"; "=shape_eqb"; "=shape_vars_lt"; "=spiece"]; ["=spieces_eqb"; "=sr_fresh"; "=sr_vars_lt"; "=vis_add"; "=vis_cost"; "=vis_here"; "=with_ss"; "=xb2"; "=xhi1"; "=xhi2"; "=xlo1"; "=xlo2"; "?LCOK"; "?Mr"; "@ren_env"; "@ren_ok"]; ["Apvars_all"; "?allow1"; "?allowA"; "?amap_den"; "?cs_ok"; "?ext1"; "?ext_list"; "?fds_ok"; "?fresh_stmt"; "?henv"; "?hid"; "?hole_ok"; "?hreplay"; "?in_allow"; "?in_ghost"; "?is_havoc"]; ["?kfoot_apart"; "?kimg_in_hull"; "?kn_bigexprs"; "?lc_guard"; "?maps_match"; "?pw_kind"; "?ren_env"; "?ren_ok"; "?sd"; "?upd"; "?utop"; "?vis"; ">cfg_of"; ">in_hull"; ">in_ivs"; ">pagedown"]; [">pageup"; ">uE"; "BELit"; "BEMd"; "BEVar"; "BKRange"; "BKWord"; "BKWr"; "BSA"; "Badenot"; "Baluop_eqb"; "Beb"; "Bedenot"; "Benv"; "Berange"; "Bev"]; ["Bexpr"; "Bexpr_eqb"; "Bitab"; "Bitab_sound"; "Bkcut"; "Bkentry"; "Bmk_sprep"; "Bmulop_eqb"; "Bridx"; "Bs_know"; "Bs_log"; "Bs_regs"; "Bsaddr"; "Bsentry"; "Bsplit_lit"; "Bsr_upd"]; ["Bsym_state"; "Btwo64"; "Bxhi"; "CelenZ"; "Cestart"; "Ckentry_ok"; "Cknow_ok"; "Cregs_ok"; "Czf_kind"; "Denv_agree"; "Dexpr_vars_lt"; "Dkentry_vars_lt"; "Dkn_vars_lt"; "Dsr_vars_lt"; "Eis_self_jump"; "Fgetr"]; ["Frdn"; "Fregupd"; "Fseg_rom"; "GTSet"; "Gt_alt2"; "Gt_eq"; "Gt_exit"; "Gt_nil"; "Hsrealizes"; "Imem_grows"; "0SEGS"; "JIn"; "JNoDup"; "Jfilter"; "Jflat_map"; "Jforallb"]; ["Jnth_error"; "Kadd"; "Kdiv"; "Kle"; "Klt"; "Kmodulo"; "Kmul"; "Kof_nat"; "Kopp"; "Kpow"; "Ksub"; "0T"; "0T'"; "0TA"; "0TA'"; "0TB"]; ["0TB'"; "0V"; "0X"; "0XB"; "0XE"; "0XN"; "0Y"; "0a"; "0ab"; "0allkn"; "0b"; "0b'"; "0b1"; "0b2"; "0bfuel"; "0bnd"]; ["0brk"; "0bs"; "0bw"; "0byteof"; "0c"; "0c1"; "0c2"; "0cA"; "0cB"; "0ca"; "0cb"; "0ch"; "0chk"; "0code"; "0cs"; "0cs'"]; ["0cs1"; "0cs2"; "0csa"; "0csb"; "0csj"; "0css"; "0d"; "0e"; "0e'"; "0eb"; "0eg"; "0en"; "0f"; "0fd"; "0fs"; "0fuel"]; ["0fw"; "0gb"; "0gh"; "0h"; "0h0"; "0hi"; "0hlz"; "0hna"; "0i"; "0i'"; "0inv"; "0iv"; "0ixs"; "0j"; "0joinpc"; "0k"]; ["0k'"; "0k1"; "0k2"; "0kb"; "0kk"; "0l"; "0l'"; "0l1"; "0l2"; "0lc"; "0len"; "0lo"; "0m"; "0m'"; "0m0"; "0mid"]; ["0mk"; "0model"; "0model'"; "0ms"; "0n"; "0n1"; "0n2"; "0nA"; "0ne"; "0nhi"; "0nlo"; "0nx"; "0nx0"; "0o"; "0o1"; "0o2"]; ["0oA"; "0oB"; "0off"; "0p"; "0r"; "0rho"; "0rs"; "0s"; "0sb"; "0scfg"; "0seen"; "0sk"; "0sn"; "0sr"; "0sr'"; "0ss"]; ["0ss'"; "LZ_to_bv"; "Lbv"; "Lbv_unsigned"; "0stop"; "0stops"; "0sz"; "0t"; "0tid"; "0tk"; "0tot"; "0ts"; "0ub"; "0uk"; "0un"; "0v"]; ["0vals"; "0w"; "0w'"; "0wb"; "0wk"; "0wn"; "0x"; "0y"; "0y'"; "0ylo"; "0z"]]).
Local Ltac lia := L5FastLia.plia.
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.
Import ListNotations.
Open Scope Z_scope.
Module APSK.
Import AX2K. Import AX2SK. Import APK.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Definition uE (E : env) (e : expr) : Z := bv_unsigned (edenot E e).
Definition pagedown (z : Z) : Z := z / 4096 * 4096.
Definition pageup (z : Z) : Z := (z + 4095) / 4096 * 4096.
Lemma pagedown_le : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "7'Q3&[3&XOr1%211%4212poF61").
Proof. intros z. unfold pagedown. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma pageup_ge : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "7'Q3&[3r1&Y0%112%4231poF61").
Proof. intros z. unfold pageup. lia. Qed.
Lemma pagedown_mod : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK ";'Q3'H&[5&XOr1%211+TP0%5221z%83921poF:1").
Proof. intros z. unfold pagedown. rewrite Z.mod_mul. reflexivity. lia. Qed.
Lemma pageup_mod : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK ";'Q3'H&[5&Y0r1%211+TP0%5221z%83921poF:1").
Proof. intros z. unfold pageup. apply Z.mod_mul. lia. Qed.
Lemma pageup_minus_pagedown : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "D'Q3&[3r2r1%3221&[:&Y0%115&XOr3%211%6241&[1%82;4+XP0%3221%?251p0=1pgFB1pg@C1").
Proof. intros a b H. unfold pageup, pagedown. lia. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Definition in_ivs (z : Z) (l : list (word * word)) : bool :=
existsb (fun iv => (bv_unsigned (fst iv) <=? z) && (z <? bv_unsigned (fst iv) + bv_unsigned (snd iv)))%bool l.
Definition in_hull (A : atable) (z : Z) : bool := ((img_lo A <=? z) && (z <? img_hi A))%bool.
Definition iv_disjoint (p q : word * word) : Prop :=
bv_unsigned (fst p) + bv_unsigned (snd p) <= bv_unsigned (fst q)
\/ bv_unsigned (fst q) + bv_unsigned (snd q) <= bv_unsigned (fst p).
Inductive seps : list (word * word) -> Prop :=
| seps_nil : seps []
| seps_cons : forall p l, Forall (iv_disjoint p) l -> seps l -> seps (p :: l).
Fixpoint sum_sizes (l : list (word * word)) : Z :=
match l with [] => 0 | iv :: r => bv_unsigned (snd iv) + sum_sizes r end.
Definition cfg_of (SEGS : list Segment) (R : bvmap 5 word) (p : Z) (M : word -> option byte) (model : Model) : config :=
mkCfg (mkst R (Z_to_bv 64 p) M (seg_rom SEGS)) model.
Section Sound.
Variable SEGS : list Segment.
Variable scfg : SpuriousCfg.
Variable IT : itab.
Hypothesis IT_ok : itab_sound SEGS IT.
Variable A : atable.
Variable nx0 : nat.
Variable LIMIT : Z.
Variable HS : nat -> option acs.
Variable XN : nat -> list expr -> acs -> option acs.
Variable XE : nat -> list expr -> acs -> option (Z * list spiece * acs).
Variable XB : nat -> list expr -> acs -> option (acs * acs).
Hypothesis SEGS_wx : wx_segs_nowrap SEGS.
Hypothesis SEGS_in_hull : forall a : word, in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None.
Definition res_len_ok : Prop := length (segments_reserved SEGS) = n_res A.
Definition hull_ok : Prop := 0 <= img_lo A /\ img_lo A mod 4096 = 0 /\ img_hi A mod 4096 = 0 /\ img_hi A <= KHI.
Definition shadow_ok : Prop := 0 <= shadow_off A <= 2 ^ 47.
Hypothesis RES_len : res_len_ok.
Hypothesis RES_hull : Forall (fun iv => img_lo A <= bv_unsigned (fst iv) /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= img_hi A) (segments_reserved SEGS).
Hypothesis HULL_ok : hull_ok.
Hypothesis SHADOW_ok : shadow_ok.
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool.
Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a /\ uE E e_sp0 <= bv_unsigned a.
Hypothesis e_sp0_init : expr_vars_lt nx0 e_sp0 = true.
Hypothesis argH_agree : forall E E' (a : word), env_agree nx0 E E' -> argH E a = argH E' a.
Hypothesis SINV_frame : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.
Variable HOLES : nat -> env -> Fs.Fs -> TSet.
Hypothesis HOLES_agree : forall h E E' fs, env_agree nx0 E E' -> HOLES h E fs = HOLES h E' fs.
Hypothesis HOLES_nil : forall h E fs, HOLES h E fs [].
Hypothesis HOLES_flat : forall h h' E E' fs, HOLES h E fs = HOLES h' E' fs.
Variable FS0 : Fs.Fs.
Variable KC : nat.
#[local] Notation CHECK := (APK.check SEGS IT A nx0 LIMIT XN XE XB HS KC).
#[local] Notation cfg := (cfg_of SEGS).
Definition Wz (fd : Z) (bs : list Z) : list event := map (fun z => WriteEv (Z_to_bv 64 fd) (Z_to_bv 8 z)) bs.
Definition piece_den (E : env) (p : spiece) : list byte :=
match p with SPLit bs => map (Z_to_bv 8) bs | SPBlob k => eb E k end.
Definition Wp (E : env) (fd : Z) (ps : list spiece) : list event :=
map (WriteEv (Z_to_bv 64 fd)) (flat_map (piece_den E) ps).
Fixpoint sd (D : TSet) (E : env) (fs : Fs.Fs) (s : shape) : TSet :=
match s with
| SNil => t_nil
| SExit c => t_exit (Z_to_bv 64 c) fs
| SEmitP fd ps s' => t_emit (Wp E fd ps) (sd D E fs s')
| SAlt2 a b => t_alt2 (sd D E fs a) (sd D E fs b)
| SCase e mid s1 s2 => if (bv_unsigned (edenot E e) <=? mid)%Z then sd D E fs s1 else sd D E fs s2
| SHole h => HOLES h E fs
| SNext => D
end.
Definition sh_lo (E : env) (p : expr * expr) : Z := shadow_off A + uE E (fst p) / 8.
Definition sh_hi (E : env) (p : expr * expr) : Z := shadow_off A + (uE E (fst p) + uE E (snd p)) / 8.
Definition allow1 (E : env) (p : expr * expr) : list (Z * Z) :=
[(pagedown (uE E (fst p)), pageup (uE E (fst p) + uE E (snd p))); (pagedown (sh_lo E p), pageup (sh_hi E p))].
Definition allowA (E : env) (cs : acs) : list (Z * Z) := flat_map (allow1 E) (a_vis cs ++ a_ghost cs).
Definition amap_den (E : env) (m : amap) : word * word := (edenot E (am_base m), edenot E (am_len m)).
Definition in_vis (E : env) (cs : acs) (z : Z) : bool :=
existsb (fun p => (uE E (fst p) <=? z) && (z <? uE E (fst p) + uE E (snd p)))%bool (a_vis cs).
Definition in_sh (E : env) (cs : acs) (z : Z) : bool :=
existsb (fun p => (sh_lo E p <=? z) && (z <? sh_hi E p))%bool (a_vis cs).
Definition in_allow (E : env) (cs : acs) (z : Z) : bool := (in_vis E cs z || in_sh E cs z)%bool.
Definition in_ghost (E : env) (cs : acs) (z : Z) : bool :=
existsb (fun p => (uE E (fst p) <=? z) && (z <? uE E (fst p) + uE E (snd p)))%bool (a_ghost cs).
Definition utop (E : env) : Z := pagedown (uE E e_sp0) - 8388608.
#[using="Type"] Lemma utop_bounds : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "D'Y='G&[3&XJr1%211&[:&Y1&SL%2251+XPPP0%5221%:271&[4&[1+TP0%22;1%4261%A261pR<C1").
Proof.
intros E. unfold utop, pagedown.
pose proof (Z.div_mod (uE E e_sp0) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (uE E e_sp0) 4096 ltac:(lia)). lia.
Qed.
#[using="Type"] Lemma utop_mod : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "<'Y='H'Q3&[5&XJr1%211+TP0%5221z%93821pR<;1").
Proof.
intros E. unfold utop. rewrite Zminus_mod, pagedown_mod. reflexivity.
Qed.
#[using="Type"] Lemma le_utop_of_aligned : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "K'Y='Q3'H&[5r1+TP0%3221z%63721&[3r2&[:&Y1r3&SL%3221+XPPP0%6221%9281&XJr4%211%=291p051p0@1poFH1pR<J1").
Proof.
intros E z Hz Hle. pose proof (utop_bounds E) as [B1 B2]. pose proof (utop_mod E) as M.
pose proof (Z.div_mod z 4096 ltac:(lia)) as Dz. pose proof (Z.div_mod (utop E) 4096 ltac:(lia)) as Du.
rewrite Hz in Dz. rewrite M in Du. lia.
Qed.
Definition vis (E : env) (cs : acs) (model : Model) (a : word) : bool :=
let h := m_vmmaps model in
let z := bv_unsigned a in
(in_hull A z
|| (utop E <=? z)
|| (in_ivs z (vm_maps h) && negb (in_ivs z (vm_noaccess h))
&& (negb (page_in_ranges (page_base a) (m_vm_lazy model)) || in_allow E cs z)))%bool.
Definition hid (E : env) (cs : acs) (model : Model) (a : word) : bool :=
(argH E a || negb (vis E cs model a))%bool.
Definition Mr (E : env) (cs : acs) (model : Model) (FULL : word -> option byte) : word -> option byte :=
mrestrict (hid E cs model) FULL.
Definition fds_std : list (word * FdEntry) :=
[(Z_to_bv 64 0, FdChannel (Z_to_bv 64 0)); (Z_to_bv 64 1, FdChannel (Z_to_bv 64 1));
(Z_to_bv 64 2, FdChannel (Z_to_bv 64 2))].
Definition CH : nat := Z.to_nat 65536.
Definition chunk (j : nat) (c : list byte) : list byte := firstn CH (skipn (CH * j) c).
Definition flen (c : list byte) : Z := Z.min (Z.of_nat (length c)) (2 ^ 26).
Definition fds3 (e : FdEntry) : list (word * FdEntry) := (Z_to_bv 64 3, e) :: fds_std.
Definition fds_ok (E : env) (f : afd) (model : Model) : Prop :=
match f with
| APK.FdStd => m_fds model = fds_std
| APK.FdDir => m_fds model = fds3 State.FdDir
| APK.FdFile k len off => exists p c,
m_fds model = fds3 (State.FdFile p (edenot E off)) /\ fs_lookup (m_fs model) p = Some c
/\ uE E len = flen c /\ uE E off <= uE E len
/\ (forall j, (65536 * Z.of_nat j < 2 ^ 26)%Z -> eb E (k + j)%nat = chunk j c)
end.
Fixpoint maps_match (E : env) (ms : list amap) (l : list (word * word)) : Prop :=
match ms with
| [] => l = []
| m :: ms' =>
if is_fog m
then maps_match E ms' l
\/ exists iv l', l = iv :: l' /\ bv_unsigned (snd iv) <= uE E (am_len m) /\ maps_match E ms' l'
else exists l', l = amap_den E m :: l' /\ maps_match E ms' l'
end.
Definition hole_ok (E : env) (ylo : Z) (l : list (word * word)) (m : amap) : Prop :=
is_hole m = true ->
(forall iv, In iv l -> bv_unsigned (fst iv) + bv_unsigned (snd iv) <= uE E (am_base m)
\/ uE E (am_base m) + uE E (am_len m) <= bv_unsigned (fst iv))
/\ (uE E (am_base m) + uE E (am_len m) <= KHI \/ ylo <= uE E (am_base m)).
#[using="Type"] Lemma holes_mono : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "Q0'Y='Q3'<'B'_2yR0%211%4211%611'S<%811'Q0&X;r5r4r2%43321r1%73921&[3%1267r7%:3198r3%=3?21p051p081pl8A1pk<D1poBL1po@M1pR<O1").
Proof.
intros E y y' l ms H Hy. apply Forall_forall. intros m Hm Hh.
destruct (proj1 (Forall_forall _ _) H m Hm Hh) as [H1 H2]. split; [exact H1 | lia].
Qed.
#[using="Type"] Lemma holes_sublist : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "Q4'Y='Q3'<'B'_2yR0%211%4211%611'S<%811'Q0&X;r5r4r3%43321r1%73921&ZK%13=36r2r6%43@21p041pjHB1r7%?315=%A3C1=p041p0<1pl8E1pk>H1pk<I1po@Q11pR<Q31").
Proof.
intros E y l l' ms H Hs. apply Forall_forall. intros m Hm Hh.
destruct (proj1 (Forall_forall _ _) H m Hm Hh) as [H1 H2]. split; [intros iv Hiv; apply H1; apply Hs; exact Hiv | exact H2].
Qed.
#[using="Type"] Lemma holes_none : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "Q1'Y='Q3'<'B'_2yR0%211%4211%611'S<%811'Q0'H'7&TKr1%211(9%63521qkJ:1%93;15&X;r5r4r3%43321r2%@3B21p081pl8C1pk<F1po@N1pR<Q01").
Proof. intros E y l ms H. apply Forall_forall. intros m Hm Hh. pose proof (proj1 (Forall_forall _ _) H m Hm) as X. congruence. Qed.
Fixpoint hreplay (E : env) (h : list hop) : list (word * word) :=
match h with
| [] => []
| HCons b n :: h' => (edenot E b, edenot E n) :: hreplay E h'
| HSub b n :: h' => maps_subtract (hreplay E h') (uE E b) (uE E b + uE E n)
end.
Definition RNA := hreplay.
Definition RLZ := hreplay.
Record cs_ok (E : env) (cs : acs) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model) : Prop := CS_OK {
co_regs : regs_ok E (s_regs (a_ss cs)) R;
co_log : s_log (a_ss cs) = [];
co_know : know_ok SEGS E (Mr E cs model FULL) (kn cs);
co_halt : m_halted model = None;
co_fds : fds_ok E (a_fd cs) model;
co_fs : m_fs model = FS0;
co_tid : a_tidset cs = false -> m_tid model = None;
co_res : vm_reserved (m_vmmaps model) = segments_reserved SEGS;
co_limit : vm_limit (m_vmmaps model) = LIMIT;
co_maps : maps_match E (a_maps cs) (vm_maps (m_vmmaps model));
co_holes : Forall (hole_ok E (a_ylo cs) (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model))) (a_maps cs);
co_seps : seps (vm_maps (m_vmmaps model));
co_wf : model_ivs_wf model;
co_bounds : Forall (fun iv => 0 < bv_unsigned (snd iv)
/\ bv_unsigned (fst iv) mod 4096 = 0 /\ bv_unsigned (snd iv) mod 4096 = 0
/\ (bv_unsigned (fst iv) + bv_unsigned (snd iv) <= img_lo A \/ img_hi A <= bv_unsigned (fst iv))
/\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= utop E) (vm_maps (m_vmmaps model));
co_lazyb : Forall (fun iv => (bv_unsigned (fst iv) + bv_unsigned (snd iv) <= img_lo A \/ img_hi A <= bv_unsigned (fst iv))
/\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= utop E) (m_vm_lazy model);
co_nasub : forall z, in_ivs z (vm_noaccess (m_vmmaps model)) = true -> in_ivs z (vm_maps (m_vmmaps model)) = true;
co_none : Forall (fun m => am_kind m = KNONE \/ am_kind m = KNONELAZY ->
In (amap_den E m) (vm_noaccess (m_vmmaps model))) (a_maps cs);
co_kinds : Forall (fun m => am_kind m = KRWLAZY ->
forall a : word, bv_unsigned (edenot E (am_base m)) <= bv_unsigned a < bv_unsigned (edenot E (am_base m)) + bv_unsigned (edenot E (am_len m)) ->
in_ivs (bv_unsigned a) (vm_noaccess (m_vmmaps model)) = false
/\ page_in_ranges (page_base a) (m_vm_lazy model) = true) (a_maps cs);
co_totsz : sum_sizes (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) <= a_totsz cs;
co_isp : bv_unsigned (vm_init_sp (m_vmmaps model)) = uE E e_sp0 /\ sp_window_lo <= uE E e_sp0 <= sp_window_hi
/\ uE E e_sppg = pagedown (uE E e_sp0);
co_brk : vm_brk (m_vmmaps model) = edenot E (a_brk cs);
co_sbrk : bv_unsigned (vm_start_brk (m_vmmaps model)) <= bv_unsigned (vm_brk (m_vmmaps model));
co_eager : eager_used model <= a_eager cs;
co_abytes : A_bytes (allowA E cs) <= a_abytes cs;
co_minv : MInv (allowA E cs) model;
co_zero : forall a : word, hid E cs model a = true ->
in_ivs (bv_unsigned a) (vm_maps (m_vmmaps model)) = true ->
in_ivs (bv_unsigned a) (vm_noaccess (m_vmmaps model)) = false ->
page_in_ranges (page_base a) (m_vm_lazy model) = true ->
in_ghost E cs (bv_unsigned a) = false ->
FULL a = Some (Z_to_bv 8 0);
co_sinv : SINV E FULL;
co_hna : vm_noaccess (m_vmmaps model) = RNA E (a_hna cs);
co_hlz : m_vm_lazy model = RLZ E (a_hlz cs);
co_tidv : a_tidset cs = true -> exists t, m_tid model = Some t /\ 0 < bv_unsigned t < PID_MAX
}.
#[using="HS XN XE XB KC"] Lemma A_wf_allowA : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK ":'Y='S6&RA&X2r2r1%3221%511phN71pR<91").
Proof.
intros E cs. unfold A_wf, allowA. apply Forall_forall. intros iv Hin.
apply in_flat_map in Hin as [p [_ Hin]]. unfold allow1 in Hin.
pose proof (u64_range (edenot E (snd p))) as Hn. pose proof (u64_range (edenot E (fst p))) as Hb.
destruct Hin as [<-|[<-|[]]]; cbn [fst snd]; unfold page_size.
- pose proof (pagedown_le (uE E (fst p))). pose proof (pageup_ge (uE E (fst p) + uE E (snd p))). unfold uE in *.
split; [lia|]. split; [apply pagedown_mod | apply pageup_mod].
- pose proof (pagedown_le (sh_lo E p)). pose proof (pageup_ge (sh_hi E p)). unfold sh_lo, sh_hi, uE in *.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
split; [lia|]. split; [apply pagedown_mod | apply pageup_mod].
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.
#[using="HS XN XE XB KC"] Lemma page_base_le : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "J'_2yR0%211'G&[3&_3&R2r1%211%4281%5293%7221&[4&[1+TP0%2261%4261'H'Q3&[5%12;6z%53421%D271%E2=1pg@G1").
Proof.
intros a. unfold page_base, page_base_of, page_size. pose proof (u64_range a) as Ha.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
assert (H : 0 <= bv_unsigned a / 4096 * 4096 <= bv_unsigned a) by lia.
rewrite u64_lit by lia. split; [lia|]. split; [lia|]. rewrite Z.mod_mul by lia. reflexivity.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.
#[using="HS XN XE XB KC"] Lemma page_in_ranges_bounds : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "QE'_2yR0%211'<'B%1233%311'Q3'Q0'G&[3r3&_3&:r1%23==1%42?1%7261&[1&C%13BB6%92D1%4261r2%>221%@281qjHE1%C3F1@'H'7&R3&R2r5%211r4%5221(D%93821r6%K2Q61%N261+1%H231+SoO%J2Q11%Q3231%Q5261p0:1p0E1pj<Q:1pkHQ;1pk<Q=1pg@QB1").
Proof.
intros a l lo hi Hl Hp. unfold page_in_ranges in Hp. apply existsb_exists in Hp as [iv [Hin Hb]].
apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
pose proof (proj1 (Forall_forall _ _) Hl iv Hin) as [L1 L2].
pose proof (page_base_le a) as (P1 & P2 & P3). unfold page_size in H2. lia.
Qed.
#[using="HS XN XE XB KC"] Lemma page_in_ranges_In : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "QE'_2yR0%211'<'B%1233%311'H'7&R3&R2r2%211r1%5221(D%93821'I'G&ZKr3%23@81&[3&_3&:%13GG<%32I1r4%52K1%7231&[1+1%2241&C%13Q0Q0E%<2Q21%62:1%?251%L1;%@2Q61%B2>1+TP0%<231%E217%J241%K281%L2A1%M2J1qjHQ;1%Q02Q<1p0Q21pk<Q=1pg@QB1").
Proof.
intros a l Hp. unfold page_in_ranges in Hp. apply existsb_exists in Hp as [iv [Hin Hb]].
apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
pose proof (page_base_le a) as (P1 & P2 & P3). unfold page_size in H2. exists iv. repeat split; try assumption; lia.
Qed.
Section SE.
Local Abbreviation SEC_T_lazy_cover_cs := (ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "Q4'Y='S6&R8y5'_2yR0%211%5241'@y8%611%311p061'QL'X4r5r4r3r2r1%6554321&RE&X:r6%23196&QO%118&X2%125=%83531p0:1pl4B1pRFD1pTNJ1phNQ11pR<Q31")) (only parsing).
Variable E : ltac:(sec_ty2 constr:(SEC_T_lazy_cover_cs) 0%nat 0%nat).
Variable cs : ltac:(sec_ty2 constr:(SEC_T_lazy_cover_cs) 1%nat 0%nat).
Variable R : ltac:(sec_ty2 constr:(SEC_T_lazy_cover_cs) 2%nat 0%nat).
Variable FULL : ltac:(sec_ty2 constr:(SEC_T_lazy_cover_cs) 3%nat 0%nat).
Variable model : ltac:(sec_ty2 constr:(SEC_T_lazy_cover_cs) 4%nat 0%nat).
Lemma lazy_cover_cs : ltac:(sec_stmt2 constr:(SEC_T_lazy_cover_cs) 5%nat 0%nat).
Proof using HS XN XE XB HULL_ok KC E cs R FULL model.
intros HC w Hlz Hh.
unfold hid in Hh. apply orb_false_iff in Hh as [Ha Hv].
apply negb_false_iff in Hv. unfold vis in Hv.
destruct (page_in_ranges_In w _ Hlz) as (iv0 & Hin0 & B1 & B2 & B3 & B4).
pose proof (proj1 (Forall_forall _ _) (co_lazyb _ _ _ _ _ HC) iv0 Hin0) as [L1 L2].
pose proof HULL_ok as HU; unfold hull_ok in HU; destruct HU as (H0 & H1 & H2 & H3).
apply orb_prop in Hv as [Hv|Hv].
- apply orb_prop in Hv as [Hv|Hv].
+ unfold in_hull in Hv. apply andb_prop in Hv as [Hv1 Hv]. apply Z.leb_le in Hv1. apply Z.ltb_lt in Hv.
exfalso. lia.
+ apply Z.leb_le in Hv.
exfalso. lia.
- apply andb_prop in Hv as [_ Hv]. rewrite Hlz in Hv. cbn [negb orb] in Hv.
pose proof (page_base_le w) as (P1 & P2 & P3).
unfold page_allowedb, allowA. apply existsb_exists. unfold page_size.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
unfold in_allow in Hv. apply orb_prop in Hv as [Hv|Hv].
+ unfold in_vis in Hv. apply existsb_exists in Hv as [p [Hin Hb]]. apply andb_prop in Hb as [Hb1 Hb2].
apply Z.leb_le in Hb1. apply Z.ltb_lt in Hb2.
exists (pagedown (uE E (fst p)), pageup (uE E (fst p) + uE E (snd p))). split.
* apply in_flat_map. exists p. split; [apply in_or_app; left; exact Hin|]. left. reflexivity.
* cbn [fst snd]. apply andb_true_intro. split; apply Z.leb_le; unfold pagedown, pageup; lia.
+ unfold in_sh in Hv. apply existsb_exists in Hv as [p [Hin Hb]]. apply andb_prop in Hb as [Hb1 Hb2].
apply Z.leb_le in Hb1. apply Z.ltb_lt in Hb2.
exists (pagedown (sh_lo E p), pageup (sh_hi E p)). split.
* apply in_flat_map. exists p. split; [apply in_or_app; left; exact Hin|]. right. left. reflexivity.
* cbn [fst snd]. apply andb_true_intro. split; apply Z.leb_le; unfold pagedown, pageup; lia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.
End SE.
#[using="SEGS_in_hull HULL_ok argH_high"] Lemma H_off_segments_cs : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK ">'Y='S6'QL&RBvZJ&X:r3r2r1%43321%7261pl491phN;1pR<=1").
Proof.
intros E cs model a Hh. unfold hid in Hh. apply orb_prop in Hh as [Ha|Hv].
- apply SEGS_in_hull. unfold in_hull. pose proof (argH_high _ _ Ha). pose proof HULL_ok as HU; unfold hull_ok in HU; destruct HU as (?&?&?&?).
unfold CEIL, KHI in *. apply andb_false_iff. right. apply Z.ltb_ge. lia.
- apply negb_true_iff in Hv. unfold vis in Hv. apply orb_false_iff in Hv as [Hv _]. apply orb_false_iff in Hv as [Hv _].
apply SEGS_in_hull. exact Hv.
Qed.
#[using="Type"] Lemma mrestrict_munrestrict_clean : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "Q2'_2yR0%211'7p021'@y8%711%311p071po>82'Hr4r1%211(D%53=21r3r2%211(1%11>%;3>31p071pg@F1&RF&RG%13?:9%32@1%B3D1;p061pkLE1pRFG1pRJM1").
Proof.
intros H FULL m' Hc. apply functional_extensionality. intros a.
unfold mrestrict, munrestrict. destruct (H a) eqn:Ha; [symmetry; apply Hc; exact Ha | reflexivity].
Qed.
#[using="Type"] Lemma vis_same : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "I'Y='S6'QL&RIr2r1%3221'H'_2yR0%211'7pg@21&XKr5r4%3321<r3%53431%<3731p0>1pl6C1pl4D1phNF1pR<H1").
Proof.
intros E cs model model' Hs. pose proof (same_but_materialized_frame _ _ Hs) as Hfr.
apply functional_extensionality. intros a. unfold vis.
replace (m_vmmaps model') with (m_vmmaps model) by (symmetry; apply Hfr).
replace (m_vm_lazy model') with (m_vm_lazy model) by (symmetry; apply Hfr). reflexivity.
Qed.
#[using="Type"] Lemma hid_same : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "I'Y='S6'QL&RIr2r1%3221'H'_2yR0%211'7pg@21&X:r5r4%3321<r3%53431%<3731p0>1pl6C1pl4D1phNF1pR<H1").
Proof. intros. unfold hid. apply functional_extensionality. intros a. rewrite (vis_same _ _ _ _ H). reflexivity. Qed.
#[using="Type"] Lemma vis_ext : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "O'Y='S6'QL'H'<'B'Y@%2211%411&S5r2%211r3%411%;3631'_2yR0%211'7pg@21&XKr5%231:<r4%4331>%F3631p0<1pl4I1pi0K1phNL1pR<N1").
Proof. intros E cs cs' model Ha. apply functional_extensionality. intros a. unfold vis, in_allow, in_vis, in_sh. rewrite Ha. reflexivity. Qed.
#[using="Type"] Lemma hid_ext : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "O'Y='S6'QL'H'<'B'Y@%2211%411&S5r2%211r3%411%;3631'_2yR0%211'7pg@21&X:r5%231:<r4%4331>%F3631p0<1pl4I1pi0K1phNL1pR<N1").
Proof. intros. unfold hid. apply functional_extensionality. intros a. rewrite (vis_ext _ _ _ _ H). reflexivity. Qed.
#[using="SINV_frame"] Lemma cs_ok_frame : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "RG'Y='S6&R8y5'_2yR0%211%5241'@y8%611%311p061'QL'Z0'X4r9r8r7r6r5%6554321&RIr2%2251'RC&X2r;r:%3221r3%6221&Z7r<&YK%11A%4331A'H'<'YM%211&YJ%11I(?%115%83531&Z6vZJr>&WMr=%2431GQ1&YI%11Q5%847631'7&X:r@r?r1%4432K1(D%I3721%Q31Q8%@1Q9%L3QF21p041pg@QM1&WF%12;Q:%QG5=1Q:QFQEp041p0B1p0L1p0Q61p0Q<1p0QD1p0QH1pl6R11pRHR31pU0R91pn2R31pl4R51pRFR71pTNR=1phNRD1pR<RF1").
Proof.
intros E cs R FULL model ss' R' FULL' model' HC Hs Hinv HR HL HK Hhid.
pose proof (same_but_materialized_frame _ _ Hs) as Hfr.
assert (Evm : m_vmmaps model' = m_vmmaps model) by apply Hfr.
assert (Elz : m_vm_lazy model' = m_vm_lazy model) by apply Hfr.
destruct HC. constructor; cbn [with_ss a_ss a_maps a_totsz a_ylo a_eager a_vis a_abytes a_brk a_fd a_tidset a_hna a_hlz kn];
rewrite ?Evm, ?Elz; try assumption.
- unfold Mr. rewrite (hid_same _ _ _ _ Hs). exact HK.
- replace (m_halted model') with (m_halted model) by (symmetry; apply Hfr). assumption.
- unfold fds_ok in *. replace (m_fds model') with (m_fds model) by (symmetry; apply Hfr).
replace (m_fs model') with (m_fs model) by (symmetry; apply Hfr). assumption.
- replace (m_fs model') with (m_fs model) by (symmetry; apply Hfr). assumption.
- intros Ht. replace (m_tid model') with (m_tid model) by (symmetry; apply Hfr). auto.
- unfold model_ivs_wf in *. rewrite Evm, Elz. assumption.
- replace (eager_used model') with (eager_used model) by (symmetry; apply Hfr). assumption.
- intros a Hh. rewrite (hid_same _ _ _ _ Hs) in Hh. rewrite (Hhid a Hh). auto.
- eapply SINV_frame; [|eassumption]. intros a Ha. apply Hhid. unfold hid. rewrite Ha. reflexivity.
- intros Ht. replace (m_tid model') with (m_tid model) by (symmetry; apply Hfr). auto.
Qed.
#[using="Type"] Lemma know_ok_filter : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "N'Y='_2yR0%211'@y8%511%311p051'YE'7p021'<%114&Z6vZJr4r3r1%544321r5&ZMr2%23>61%:49481p061pk0=1piJ@1pTDD1pR<M1").
Proof.
intros E M f k HK. unfold know_ok in *. apply Forall_forall. intros K Hin.
apply filter_In in Hin as [Hin _]. exact (proj1 (Forall_forall _ _) HK K Hin).
Qed.
#[using="Type"] Lemma cs_ok_set_kn : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "Q:'Y='S6&R8y5'_2yR0%211%5241'@y8%611%311p061'QL'<'YE%211'X4r6r5r4r3r2%6554321&Z6vZJr7&WM%142:78%544317r8&W8%126;%@531?>=p051p0<1pk2D1pl4H1pRFJ1pTNQ01phNQ71pR<Q91").
Proof.
intros E cs R FULL model k' HC HK.
destruct HC; constructor; cbn [set_kn with_ss a_ss a_maps a_totsz a_ylo a_eager a_vis a_abytes a_brk a_fd a_tidset a_hna a_hlz kn mk_ss s_regs s_log s_know];
try assumption; reflexivity.
Qed.
#[using="Type"] Lemma cs_gc_ok : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "Q2'='Y='S6&R8y5'_2yR0%211%5241'@y8%611%311p061'QL'X4r5r4r3r2r1%6554321r6&SDr7%2219%;541987p061pl4>1pRF@1pTNF1phNM1pR<O1pj4Q11").
Proof.
intros gb E cs R FULL model HC. unfold cs_gc. destruct (split_lit (reg cs 2)) as [spb spk].
apply cs_ok_set_kn; [exact HC|]. apply know_ok_filter. exact (co_know _ _ _ _ _ HC).
Qed.
#[using="Type"] Lemma mk_itab_ranges_acc_sound : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "C'<'B'Q3'=%3221%511&YB&YCvZJr1%3221&UNr3r2%33621%8271p061pn@;1pm>=1").
Proof.
induction rs as [|[lo n] rs IH]; intros t Ht; cbn [mk_itab_ranges_acc]; [exact Ht|].
apply IH. apply mk_itab_fuel_sound. exact Ht.
Qed.
#[using="Type"] Lemma mk_itab_ranges_sound : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "='<'B'Q3'=%3221%511&YCvZJ&UMr1%2231%5241pm>71").
Proof.
intros rs. unfold mk_itab_ranges. apply mk_itab_ranges_acc_sound.
intros pc i. unfold itab_lookup. destruct pc; try discriminate. rewrite pt_get_leaf. discriminate.
Qed.
#[using="Type"] Lemma pc_set_kn : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "@'S6'<'YE%211'H'Q3&VL&W8r2r1%3221%511%614%93821pk0;1phN?1").
Proof. reflexivity. Qed.
#[using="Type"] Lemma pc_cs_gc : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK ">'='S6'H'Q3&VL&SDr2r1%3221%511%613%93821phN;1pj4=1").
Proof. intros gb cs. unfold cs_gc. destruct (split_lit (reg cs 2)); reflexivity. Qed.
#[using="Type"] Lemma drop_ixs_incl : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "C'<'=%211'YE%411&ZKr1&SKr4r3r2%43321%73961%83:34p021pS8<1pk0<1pjB@1pjJ@1").
Proof.
intros ixs i k. revert i. induction k as [|K' r IH]; intros i K Hin; cbn [drop_ixs] in Hin.
- exact Hin.
- destruct (existsb (Nat.eqb i) ixs).
+ right. eapply IH. exact Hin.
+ destruct Hin as [<-|Hin]; [left; reflexivity | right; eapply IH; exact Hin].
Qed.
#[using="Type"] Lemma forget_sound : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "Q8'Y='S6&R8y5'_2yR0%211%5241'@y8%611%311p061'QL'<'=%211'X4r6r5r4r3r2%6554321r7&W8&SK(2&U7%11;%43831%62=1%?581=<;p0:1pjJB1pl4F1pRFH1pTNN1phNQ51pR<Q71").
Proof.
intros E cs R FULL model ixs HC. apply cs_ok_set_kn; [exact HC|].
unfold know_ok. apply Forall_forall. intros K Hin. apply drop_ixs_incl in Hin.
exact (proj1 (Forall_forall _ _) (co_know _ _ _ _ _ HC) K Hin).
Qed.
Definition kfoot (E : env) (K : kentry) : option (Z * Z) :=
match K with
| KWord a w _ => Some (estart E a, Z.of_nat w)
| KZero a l => Some (estart E a, elenZ E l)
| KBlob a l _ => Some (estart E a, elenZ E l)
| KImg lo hi => Some (lo, hi - lo)%Z
| KWr a n => Some (estart E a, elenZ E n)
| KFill a l _ => Some (estart E a, elenZ E l)
| KUnk a l => Some (estart E a, elenZ E l)
| KAlign _ _ | KRange _ _ _ | KDisj _ _ _ _ => None
end.
Definition kfoot_apart (E : env) (K : kentry) (lo n : Z) : Prop :=
match kfoot E K with
| None => True
| Some (s, l) => (s + l <= lo \/ lo + n <= s)%Z
end.
Section SE.
Local Abbreviation SEC_T_kentry_keep_sem := (ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "QD'Y='_2yR0%211'@y8%511%311p051po>62'YE'Q3&Z5vZJr6r5r3%544321&X@r7r4r2%443261'L&[4&_3r1%22I1%421=&[3&[1%12@;%3215%:251'Hr8%11?r9%11A%53Q031p071po>Q61%N4M5GLp021p0F1p0L1pl:Q31pkHQ41pS8Q61pTFQ81pTDQ:1pR<QC1")) (only parsing).
Variable E : ltac:(sec_ty2 constr:(SEC_T_kentry_keep_sem) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_kentry_keep_sem) 1%nat 0%nat).
Variable M' : ltac:(sec_ty2 constr:(SEC_T_kentry_keep_sem) 2%nat 0%nat).
Lemma kentry_keep_sem : ltac:(sec_stmt2 constr:(SEC_T_kentry_keep_sem) 3%nat 0%nat).
Proof using Type E M M'.
intros K lo n HK Hap Hout.
assert (RD : forall (a : word) k, (bv_unsigned a + Z.of_nat k <= 2 ^ 64)%Z ->
(bv_unsigned a + Z.of_nat k <= lo \/ lo + n <= bv_unsigned a)%Z ->
rdn SEGS M' a k = rdn SEGS M a k).
{ intros a k Hnw Hd. apply rdn_ext; [exact Hnw|]. intros x Hx. apply Hout. lia. }
unfold kfoot_apart, kfoot in Hap.
destruct K as [[b k] w v|[b k] nn|[b k] nn kb|ilo ihi|e m|e rlo rhi|[b k] nn|a1 n1 a2 n2|[b k] nn fc|[b k] nn]; cbn [kentry_ok] in *;
try exact HK.
7: { destruct HK as [Hfl Hz]. split; [exact Hfl|]. intros i Hi.
destruct Hfl as (F1 & F2 & F3 & F4).
rewrite Hout; [apply Hz; exact Hi|]. rewrite u64_lit by lia. lia. }
6: { destruct HK as [Hfl Hz]. split; [exact Hfl|]. intros i Hi.
destruct Hfl as (F1 & F2 & F3 & F4).
rewrite Hout; [apply Hz; exact Hi|]. rewrite u64_lit by lia. lia. }
- destruct HK as (Hw & Hfl & Hrd). split; [exact Hw|]. split; [exact Hfl|].
rewrite RD; [exact Hrd | rewrite (flat_u E _ _ Hfl); destruct Hfl; lia | rewrite (flat_u E _ _ Hfl); lia].
- destruct HK as [Hfl Hz]. split; [exact Hfl|]. intros i Hi.
destruct Hfl as (F1 & F2 & F3 & F4).
rewrite Hout; [apply Hz; exact Hi|]. rewrite u64_lit by lia. lia.
- destruct HK as (Hfl & Hlen & Hz). split; [exact Hfl|]. split; [exact Hlen|]. intros i Hi.
destruct Hfl as (F1 & F2 & F3 & F4).
rewrite Hout; [apply Hz; exact Hi|]. rewrite u64_lit by lia. lia.
- destruct HK as (HA & HB & HC). split; [exact HA|]. split; [exact HB|]. intros i Hi.
rewrite Hout; [apply HC; lia|]. rewrite u64_lit by lia. lia.
- destruct HK as [Hfl Hs]. split; [exact Hfl|]. intros d m Hd0 Hdm.
pose proof (Hs d m Hd0 Hdm) as H. destruct Hfl as (F1 & F2 & F3 & F4).
destruct m as [|m']; [reflexivity|].
apply store_ok_of_all; [rewrite u64_lit by lia; lia|].
intros x Hx. rewrite u64_lit in Hx by lia.
unfold wview. rewrite Hout by lia. fold (wview SEGS M x).
eapply (store_ok_all SEGS M (Datatypes.S m')); [| exact H |]; rewrite u64_lit by lia; lia.
Qed.
End SE.
#[using="Type"] Lemma elenZ_lit : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "I'Y='Q3'G&[3zr1%3221&[4&[9+2+R0%3221%5271%;271'H&Z3r3(Y2r2%211%5241%73D13p091poFF1pR<H1").
Proof. intros E z Hz. unfold elenZ. cbn [edenot]. rewrite u64_lit by lia. reflexivity. Qed.
#[using="Type"] Lemma kentry_apart_b_sem : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "Q?'Y='_2yR0%211'@y8%511%311p051'<'YE%211'Y@'Q3&Z6vZJr7r6r5%544321'H'7&TNr4r3r2%4593218(D%83721&X@r9&Z4(Y8%12?:%3241&Z3%126<%847D31p0:1p0D1pnNL1pnLL1pnJN1pS8Q11pgDQ11pTDQ51pR<Q>1").
Proof.
intros E M allkn K ub uk un Hall Hb. unfold kfoot_apart, kfoot.
destruct K as [[b k] w v|[b k] nn|[b k] nn kb|ilo ihi|e m|e rlo rhi|[b k] nn|a1 n1 a2 n2|[b k] nn fc|[b k] nn]; cbn [kentry_apart_b] in Hb;
try exact I; try discriminate.
7: { pose proof (ranges_apart_x_sound SEGS E M allkn _ _ _ _ _ _ Hall Hb). lia. }
6: { pose proof (ranges_apart_x_sound SEGS E M allkn _ _ _ _ _ _ Hall Hb). lia. }
- apply andb_prop in Hb as [Hw Hb]. apply Nat.leb_le in Hw.
pose proof (ranges_apart_x_sound SEGS E M allkn _ _ _ _ _ _ Hall Hb) as Hd.
rewrite (elenZ_lit E (Z.of_nat w)) in Hd by lia. lia.
- pose proof (ranges_apart_x_sound SEGS E M allkn _ _ _ _ _ _ Hall Hb). lia.
- pose proof (ranges_apart_x_sound SEGS E M allkn _ _ _ _ _ _ Hall Hb). lia.
- apply andb_prop in Hb as [Hb Hap]. apply andb_prop in Hb as [Hb Hlt]. apply andb_prop in Hb as [H0 Hl].
apply Z.leb_le in H0. apply Z.leb_le in Hl. apply Z.ltb_lt in Hlt. unfold two64 in Hlt.
pose proof (ranges_apart_x_sound SEGS E M allkn _ _ _ _ _ _ Hall Hap) as Hd.
rewrite (elenZ_lit E (ihi - ilo)) in Hd by lia.
unfold estart in Hd at 2 3. cbn [a_base a_off edenot] in Hd.
rewrite !u64_lit in Hd by lia. lia.
- pose proof (ranges_apart_x_sound SEGS E M allkn _ _ _ _ _ _ Hall Hb). lia.
Qed.
#[using="Type"] Lemma kentry_apart_keep : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "R8'Y='_2yR0%211'@y8%511%311p051po>62'<'YE%211'Y@'Q3&Z6vZJr8r7r5%544321&Z5r9%247164'H'7&TNr4r3r6%45<;321(D%83721'L&[4&_3r1%22Q31&Z4r<(Y8%12G<%4231%9261&[3&[1&Z3%128L%3261%521<%A271r;r2%211%?12%O3Q@21p061po>QF1r:%Q64Q;D1Q:p031p0M1p0Q71p0Q;1pnNQC1pnLQC1pnJQE1pS8QH1pgDQH1pTFQL1pTDQN1pR<R71").
Proof.
intros E M M' allkn K ub uk un Hall HK Hb Hout.
eapply kentry_keep_sem; [exact HK | eapply kentry_apart_b_sem; [exact Hall | exact Hb] | exact Hout].
Qed.
#[using="Type"] Lemma know_ok_filter_apart : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "RA'Y='_2yR0%211'@y8%511%311p051'<'YE%211'7p031'Y@'Q3&Z6vZJr8r7r5%544321&ZKr1%23>15'Hr2%811(D%43A21'L&TNr9r6r3%453@2?1%;3H18&Z5r<r:%34G216%;251p0=1p0C1pS8Q21&[4&_3%12Q=H&Z4r;(Y8%12BO%4231%8261&[3&[1&Z3r4%2291%4271%621=%O281%G1Q4%>1Q5%Q73QI21p041po>QO1&ZM%13QJQAQB%QE4QDDQ51p041p0K1p0QC1pnNQK1pnLQK1pnJQM1piJQO1pk0R21pTFR61pTDR71pR<R@1").
Proof.
intros E M M' k f ub uk un HK Hf Hout. unfold know_ok. apply Forall_forall. intros K Hin.
apply filter_In in Hin as [Hin Hfk].
pose proof (proj1 (Forall_forall _ _) HK K Hin) as HKK.
destruct (Hf K Hin Hfk) as [Hap | Hdone]; [|exact Hdone].
eapply kentry_apart_keep; eassumption.
Qed.
#[using="Type"] Lemma kentry_apart_bp_eq : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "H'<'YE%211'Y@'Q3'H'7&TOr5&YFr4r3r2%445321r1%86725431&TN%1597653%=3<31pS8B1pnNA1pnLA1pnJC1pgDE1").
Proof.
intros allkn ub uk un K. destruct K as [[kb kk] w' v|[kb kk] len|[kb kk] len bk|lo hi|e' m'|e' lo' hi'|[eb ek] en|c1 m1 c2 m2|[kb kk] len fc|[kb kk] len];
cbn [kentry_apart_bp kentry_apart_b]; rewrite ?ranges_apart_p_eq; reflexivity.
Qed.
#[using="Type"] Lemma havoc1p_eq : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "G'<'YE%211'Y@'Q3'H&T<r5&YFr4r3r2%445321r1%86725431&T;%1597653%<3?31pS8A1pnN@1pnL@1pnJB1pk0D1").
Proof. intros. unfold havoc1p, havoc1. rewrite kentry_apart_bp_eq. reflexivity. Qed.
#[using="Type"] Lemma know_ok_havoc : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "R1'Y='_2yR0%211'@y8%511%311p051po>62'<'YE%211'Y@'Q3&Z6vZJr7r6r4%544321'L&[4&_3r1%22G1&Z4r9(Y8r5%221;%5241%:271&[3&[1&Z3r3%22:1%4271%621>%C281'Hr8r2%211%B12%53Q721p071po>Q=1&ZI%128Q1r:&U;%14Q4Q3HQ2%Q74Q63<1p051p081p0Q51pl:Q=1plLQ=1pgFQ?1pk0QA1pTFQE1pTDQG1pR<R01").
Proof.
intros E M M' k b o n HK Hout Hg. unfold kn_havoc, know_ok. cbv zeta.
apply Forall_flat_map. apply Forall_forall. intros K Hin.
pose proof (proj1 (Forall_forall _ _) HK _ Hin) as HKK.
rewrite havoc1p_eq. unfold havoc1.
destruct (kwr_b K || kentry_apart_b k b o n K)%bool eqn:Hf.
- apply Forall_one. apply orb_prop in Hf as [Hw|Ha].
+ destruct K as [| | | | | |[wb wk] wn| | |]; try discriminate.
destruct HKK as [Hfl Hs]. cbn [kentry_ok]. split; [exact Hfl|].
intros d m Hd Hdm. eapply store_ok_mono; [exact Hg | apply Hs; assumption].
+ eapply kentry_apart_keep; eassumption.
- destruct K as [|[kb kk] len| | | | | | |[kb kk] len fc|[kb kk] len]; try constructor.
+ eapply kzero_cut_sound; [exact HK | exact HKK | exact Hout].
+ eapply kfill_cut_sound; [exact HK | exact HKK | exact Hout].
+ eapply kunk_cut_sound; [exact HK | exact HKK | exact Hout].
Qed.
Definition pw_kind (mk : saddr -> expr -> kentry) (P : (word -> option byte) -> word -> Prop) : Prop :=
forall E M a n,
kentry_ok SEGS E M (mk a n)
<-> (flat E a (elenZ E n) /\ forall i, (0 <= i < elenZ E n)%Z -> P M (Z_to_bv 64 (estart E a + i))).
#[using="Type"] Lemma pw_kind_zf : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "O'YL'Y@'YEp021p041'@'_2y8%211%411!p021&Z8vZJr2r1%43321&XEr3yR0%>11p01<r4%918%211qo>51qTD51%:291p0<1ph8B1pl2J1").
Proof. intros mk byteof H E M a n. exact (H E M a n). Qed.
#[using="Type"] Lemma pw_kind_wr : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "H&XE(Y7'_2yR0%211'@y8%511%311p051&K'H&QKvZJr2r1%43321(1%11;%83;31%:11qo>A1qTD=1%G2F1").
Proof.
intros E M a n. cbn [kentry_ok]. split; intros [Hfl H]; split; try exact Hfl.
- intros i Hi. pose proof (H i 1%nat ltac:(lia) ltac:(cbn; lia)) as S1. cbn [store_ok] in S1.
destruct (wview SEGS M (Z_to_bv 64 (estart E a + i))); [discriminate | discriminate].
- intros d m Hd Hdm. pose proof Hfl as Hfl0. destruct Hfl as (F1 & F2 & F3 & F4).
destruct m as [|m']; [reflexivity|]. set (m := Datatypes.S m') in *.
assert (Hm : 1 <= Z.of_nat m) by (subst m; rewrite Nat2Z.inj_succ; lia).
assert (Hu : bv_unsigned (Z_to_bv 64 (estart E a + d)) = estart E a + d) by (apply u_small; lia).
apply store_ok_of_all; rewrite Hu; [lia|].
intros x Hx. replace x with (Z_to_bv 64 (estart E a + (bv_unsigned x - estart E a))).
+ apply H. lia.
+ apply bv_eq. rewrite u_small; [lia|]. pose proof (u64_range x). lia.
Qed.
#[using="Type"] Lemma kcut_pw_sound : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "RI'YL'Y@'YEp021p041'_2yR0%211'@y8%511%311p051!p071p031'Y='<%11@'Q3&XEr=r<%3221&Z6vZJr;r8%443621&Z5r?(Y8r5r4%3221r3%6221%84<@;1'L&[4&_3r1%22Q41&Z4r:r9%?221%42A1%9261&[3&[1&Z3%12FI%3261%521<%A271rAr>r2%3221rB%124Jp031p081po>QI1'Q0%Q53Q9Q4Q<&YDr7r6%38>Q<JIQ;21Q6%63R551p081p0Q41p0Q>1p0QD1pkFR;1pk:QJ1pk8R=1po<R>1po:QM1po8R@1pgDR01pTFR71pTDR81pTHR91pR<R61pTLR81pl2RD1").
Proof.
intros mk P E M0 M M' allkn wb wk wn kb kk len Hkind Hall HK Hout.
apply (proj1 (Hkind E M _ _)) in HK. destruct HK as [Hfl Hz].
unfold kcut.
set (ws := mkAlu ALU_ADD wb (ELit wk)). set (ks := mkAlu ALU_ADD kb (ELit kk)).
assert (Uws : eqm (bv_unsigned (edenot E ws)) (estart E (SA wb wk))).
{ subst ws. rewrite mkAlu_denot. unfold estart; cbn [a_base a_off edenot].
eapply eqm_trans; [apply u_add_eqm|]. apply eqm_add; [apply eqm_refl|apply eqm_u_lit]. }
assert (Uks : eqm (bv_unsigned (edenot E ks)) (estart E (SA kb kk))).
{ subst ks. rewrite mkAlu_denot. unfold estart; cbn [a_base a_off edenot].
eapply eqm_trans; [apply u_add_eqm|]. apply eqm_add; [apply eqm_refl|apply eqm_u_lit]. }
pose proof Hfl as Hfl0. destruct Hfl as (F1 & F2 & F3 & F4).
apply Forall_app; split.
-
destruct (lin_ge0 allkn [(kb, kk)] [(wb, wk)]); [constructor|].
destruct (lin_ge0 allkn [(wb, wk)] [(kb, kk)]) eqn:H1; [|constructor].
destruct (lin_ge0 allkn [(kb, kk); (len, 0%Z)] [(wb, wk)]) eqn:H2; [|constructor].
pose proof (lin_ge0_sound SEGS E M0 allkn _ _ Hall H1) as A0. cbn [xt_den] in A0.
pose proof (lin_ge0_sound SEGS E M0 allkn _ _ Hall H2) as B0. cbn [xt_den] in B0.
constructor; [|constructor]. apply (proj2 (Hkind E M' _ _)).
assert (HL : elenZ E (mkAlu ALU_SUB ws ks) = (estart E (SA wb wk) - estart E (SA kb kk))%Z).
{ unfold elenZ. rewrite mkAlu_denot.
assert (eqm (bv_unsigned (alu64 ALU_SUB (edenot E ws) (edenot E ks))) (estart E (SA wb wk) - estart E (SA kb kk))) as [q Hq].
{ eapply eqm_trans; [apply u_sub_eqm|]. apply eqm_add; [exact Uws|]. destruct Uks as [q Hq]. exists (-q)%Z. lia. }
pose proof (u64_range (alu64 ALU_SUB (edenot E ws) (edenot E ks))) as R.
pose proof (u64_range (edenot E len)) as RL.
unfold flat, estart, elenZ in *; cbn [a_base a_off] in *. lia. }
rewrite HL. split.
+ unfold flat in *. unfold estart, elenZ in *; cbn [a_base a_off] in *. lia.
+ intros i Hi. apply Hout; [|apply Hz]; unfold estart, elenZ in *; cbn [a_base a_off] in *; [|lia].
left. rewrite u_small; lia.
-
destruct (lin_ge0 allkn [(kb, kk); (len, 0%Z)] [(wb, wk); (wn, 0%Z)]) eqn:H1; [|constructor].
destruct (lin_ge0 allkn [(wb, wk); (wn, 0%Z)] [(kb, kk)]) eqn:H2; [|constructor].
destruct (lin_ge0 allkn [(ELit 0, (two64 - 1)%Z)] [(kb, kk); (len, 0%Z)]) eqn:H3; [|constructor].
pose proof (lin_ge0_sound SEGS E M0 allkn _ _ Hall H1) as A0. cbn [xt_den] in A0.
pose proof (lin_ge0_sound SEGS E M0 allkn _ _ Hall H2) as B0. cbn [xt_den] in B0.
pose proof (lin_ge0_sound SEGS E M0 allkn _ _ Hall H3) as C0. cbn [xt_den edenot] in C0.
rewrite u_lit0 in C0. unfold two64 in C0.
cbv zeta.
set (we := mkAlu ALU_ADD ws wn).
assert (Uwe : eqm (bv_unsigned (edenot E we)) (estart E (SA wb wk) + elenZ E wn)).
{ subst we. rewrite mkAlu_denot. eapply eqm_trans; [apply u_add_eqm|]. apply eqm_add; [exact Uws|apply eqm_refl]. }
destruct (split_lit we) as [hb ho] eqn:Hsp.
lazymatch goal with |- Forall _ [mk ?ha0 _] => set (ha := ha0) end.
assert (Hst : estart E ha = (estart E (SA wb wk) + elenZ E wn)%Z).
{ subst ha.
destruct (lin_ge0 allkn [(hb, ho)] [(wb, wk); (wn, 0%Z)] && lin_ge0 allkn [(wb, wk); (wn, 0%Z)] [(hb, ho)])%bool eqn:Hh.
- apply andb_prop in Hh as [Hh1 Hh2].
pose proof (lin_ge0_sound SEGS E M0 allkn _ _ Hall Hh1) as C1. cbn [xt_den] in C1.
pose proof (lin_ge0_sound SEGS E M0 allkn _ _ Hall Hh2) as C2. cbn [xt_den] in C2.
unfold estart, elenZ in *; cbn [a_base a_off] in *. lia.
- unfold estart at 1; cbn [a_base a_off]. rewrite Z.add_0_r.
destruct Uwe as [q Hq]. pose proof (u64_range (edenot E we)).
pose proof (u64_range (edenot E len)) as RL.
unfold flat, estart, elenZ in *; cbn [a_base a_off] in *. lia. }
assert (HL : elenZ E (mkAlu ALU_SUB (mkAlu ALU_ADD ks len) we)
= (estart E (SA kb kk) + elenZ E len - (estart E (SA wb wk) + elenZ E wn))%Z).
{ unfold elenZ at 1. rewrite mkAlu_denot.
assert (eqm (bv_unsigned (alu64 ALU_SUB (edenot E (mkAlu ALU_ADD ks len)) (edenot E we)))
(estart E (SA kb kk) + elenZ E len - (estart E (SA wb wk) + elenZ E wn))) as [q Hq].
{ eapply eqm_trans; [apply u_sub_eqm|]. apply eqm_add.
- rewrite mkAlu_denot. eapply eqm_trans; [apply u_add_eqm|]. apply eqm_add; [exact Uks|apply eqm_refl].
- destruct Uwe as [q Hq]. exists (-q)%Z. lia. }
pose proof (u64_range (alu64 ALU_SUB (edenot E (mkAlu ALU_ADD ks len)) (edenot E we))) as R.
pose proof (u64_range (edenot E len)) as RL.
unfold flat, estart, elenZ in *; cbn [a_base a_off] in *. lia. }
constructor; [|constructor]. apply (proj2 (Hkind E M' _ _)). rewrite HL.
split.
+ unfold flat. rewrite Hst. pose proof (u64_range (edenot E len)) as RL.
unfold flat, estart, elenZ in *; cbn [a_base a_off] in *. lia.
+ intros i Hi. rewrite Hst.
apply Hout.
* right. pose proof (u64_range (edenot E len)) as RL.
rewrite u_small; unfold flat, estart, elenZ in *; cbn [a_base a_off] in *; lia.
* replace (estart E (SA wb wk) + elenZ E wn + i)%Z
with (estart E (SA kb kk) + (estart E (SA wb wk) + elenZ E wn - estart E (SA kb kk) + i))%Z by lia.
apply Hz. unfold estart, elenZ in *; cbn [a_base a_off] in *. lia.
Qed.
#[using="Type"] Lemma kwr_cut_sound : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "R>'Y='_2yR0%211'@y8%511%311p051po>62'<'YE%211'Y@'Q3&Z6vZJr;r:r7%544321&Z5r<(Y7(Y8r4r3%3221r2%6221%94>8<1'L&[4&_3r1%22Q11&Z4r>r9r8%@221%5241%:271&[3&[1&Z3%129K%3261%521=%B271'H%M1Gr=%11I%43Q?31p061po>QE1'Q0%Q53Q:EQ9&UBr6r5%37Q<HGQ;21Q5%63QD51p081p0Q31p0Q>1pkFQF1pk:QF1pk8QH1po<QI1po:QI1po8QK1pgDQM1pTFR11pTDR31pTHR41pR<R=1").
Proof.
intros. eapply (kcut_pw_sound KWr _ E M0 M M'); [apply pw_kind_wr | eassumption | eassumption |].
intros x Hx HP. unfold wview in *. rewrite (H1 x Hx). exact HP.
Qed.
#[using="Type"] Lemma cutout1p_eq : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "G'<'YE%211'Y@'Q3'H&SGr5&YFr4r3r2%445321r1%86725431&SF%1597653%<3?31pS8A1pnN@1pnL@1pnJB1pk0D1").
Proof. intros. unfold cutout1p, cutout1. rewrite kentry_apart_bp_eq. reflexivity. Qed.
#[using="Type"] Lemma know_ok_cutout : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "QM'Y='_2yR0%211'@y8%511%311p051po>62'<'YE%211'Y@'Q3&Z6vZJr7r6r4%544321'L&[4&_3r1%22G1&Z4r9(Y8r5%221;%5241%:271&[3&[1&Z3r3%22:1%4271%621>%C281'Hr8r2%211%B12%53Q721p071po>Q=1&U:%14Q0EO>%Q44Q3HQ21p041p0Q11pl:Q91plLQ91pgFQ;1pk0Q=1pTFQA1pTDQC1pR<QL1").
Proof.
intros E M M' k b o n HK Hout. unfold kn_cutout, know_ok. cbv zeta.
apply Forall_flat_map. apply Forall_forall. intros K Hin.
pose proof (proj1 (Forall_forall _ _) HK _ Hin) as HKK.
rewrite cutout1p_eq. unfold cutout1.
destruct (kentry_apart_b k b o n K) eqn:Hf.
- apply Forall_one. eapply kentry_apart_keep; eassumption.
- destruct K as [|[kb kk] len| | | | |[kb kk] len| |[kb kk] len fc|[kb kk] len]; try constructor.
+ eapply kzero_cut_sound; [exact HK | exact HKK | exact Hout].
+ eapply kwr_cut_sound; [exact HK | exact HKK | exact Hout].
+ eapply kfill_cut_sound; [exact HK | exact HKK | exact Hout].
+ eapply kunk_cut_sound; [exact HK | exact HKK | exact Hout].
Qed.
#[using="Type"] Lemma droprange_sound : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "Q3'Y='S6&R8y5'_2yR0%211%5241'@y8%611%311p061'QL'Y@'X4r7r6r5r4r3%6554321r8&V:r2%23951%;541987p061pl:>1pgF?1pl4A1pRFC1pTNI1phNQ01pR<Q21").
Proof.
intros E cs R FULL model b n HC. unfold node_droprange. destruct (split_lit b) as [bb bk].
apply cs_ok_set_kn; [exact HC|]. eapply know_ok_havoc; [exact (co_know _ _ _ _ _ HC) | intros; reflexivity | apply mem_grows_refl].
Qed.
#[using="Type"] Lemma bump_sound : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "QA'Y='S6&R8y5'_2yR0%211%5241'@y8%611%311p061'QL'='X4r7r6r5r4r3%6554321'H%?1F&V6%1295(4r2%22K1%73641'Gr9%A51<@?>'Q3&VL%11?r8%311%@3531%9271p0;1p0D1pi0Q91pkJM1pl4O1pRFQ11pTNQ71phNQ>1pR<Q@1").
Proof.
intros E cs R FULL model m cs' HC H. unfold node_bump in H. destruct (Nat.leb (nxt cs) m); [|discriminate]. injection H as <-.
split; [|reflexivity].
destruct HC; constructor; cbn [bump with_ss a_ss mk_ss s_regs s_log s_know kn a_maps a_totsz a_ylo a_eager a_vis a_abytes a_brk a_fd a_tidset a_hna a_hlz];
try assumption; reflexivity.
Qed.
#[using="Type"] Lemma mkind_eqb_eq : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK ">'UO'H'7&V0r2r1%3221(D%73621r3%93:16p031pgF<1pg@=1").
Proof. intros [] []; cbn; intros; first [reflexivity | discriminate]. Qed.
#[using="Type"] Lemma kentry_eqb_eq : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK ">'YE'H'7&U0r2r1%3221(D%73621r3%93:16p031po@<1po>=1").
Proof.
intros x y H. destruct x, y; cbn [kentry_eqb] in H; try discriminate;
repeat match goal with
| H : (_ && _)%bool = true |- _ => apply andb_prop in H; destruct H
end;
repeat match goal with
| H : saddr_eqb _ _ = true |- _ => apply saddr_eqb_eq in H
| H : expr_eqb _ _ = true |- _ => apply expr_eqb_eq in H
| H : Nat.eqb _ _ = true |- _ => apply Nat.eqb_eq in H
| H : Z.eqb _ _ = true |- _ => apply Z.eqb_eq in H
end; subst; reflexivity.
Qed.
#[using="Type"] Lemma amap_eqb_eq : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK ">'S<'H'7&S=r2r1%3221(D%73621r3%93:16p031po@<1po>=1").
Proof.
intros [b l k] [b' l' k'] H. unfold amap_eqb in H. cbn [am_base am_len am_kind] in H.
apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
apply expr_eqb_eq in H1. apply expr_eqb_eq in H2. apply mkind_eqb_eq in H3. congruence.
Qed.
#[using="Type"] Lemma hop_eqb_eq : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK ">'T?'H'7&TAr2r1%3221(D%73621r3%93:16p031po@<1po>=1").
Proof.
intros [b n|b n] [b' n'|b' n'] H; cbn [hop_eqb] in H; try discriminate;
apply andb_prop in H as [H1 H2]; apply expr_eqb_eq in H1; apply expr_eqb_eq in H2; congruence.
Qed.
#[using="Type"] Lemma pair_eqb_eq : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "@'B'Y@%2211'H'7&VJr2r1%3221(D%73621r3%93:16p031po@<1po>=1").
Proof.
intros [a b] [a' b'] H. unfold pair_eqb in H. cbn [fst snd] in H. apply andb_prop in H as [H1 H2].
apply expr_eqb_eq in H1. apply expr_eqb_eq in H2. congruence.
Qed.
#[using="Type"] Lemma afd_eqb_eq : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK ">'S8'H'7&S9r2r1%3221(D%73621r3%93:16p031po@<1po>=1").
Proof.
intros [|k l o|] [|k' l' o'|] H; cbn [afd_eqb] in H; try discriminate; try reflexivity.
apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
apply Nat.eqb_eq in H1. apply expr_eqb_eq in H2. apply expr_eqb_eq in H3. congruence.
Qed.
#[using="Type"] Lemma list_eqb_eq : forall {T} (eqb : T -> T -> bool), (forall x y, eqb x y = true -> x = y) ->
forall x y, list_eqb eqb x y = true -> x = y.
Proof.
intros T eqb Heq x. induction x as [|a x IH]; intros [|b y] H; cbn [list_eqb] in H; try discriminate; [reflexivity|].
apply andb_prop in H as [H1 H2]. rewrite (Heq _ _ H1), (IH _ H2). reflexivity.
Qed.
Definition kimg_in_hull (k : list kentry) : Prop :=
Forall (fun K => match K with KImg lo hi => img_lo A <= lo /\ hi <= img_hi A | _ => True end) k.
#[using="Type"] Lemma kimg_clip_in_hull : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK ":'<'YE%211&XA&U5v0r1%3221%511pk071").
Proof.
intros k. unfold kimg_in_hull, kimg_clip. apply Forall_forall. intros K Hin. apply filter_In in Hin as [_ Hb].
destruct K; try exact I. apply andb_prop in Hb as [Hb H3]. apply andb_prop in Hb as [H1 H2].
apply Z.leb_le in H1. apply Z.leb_le in H3. lia.
Qed.
#[using="Type"] Lemma kimg_clip_incl : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "?'<'YE%211&ZKr1&U5v0r2%3221%63851r3%83:41p031pS8<1pk0<1").
Proof. intros k K H. unfold kimg_clip in H. apply filter_In in H as [H _]. exact H. Qed.
#[using="Type"] Lemma kimg_in_hull_app : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "?'<'YE%211&XAr2%211&6r4r3%33821%711p061p071pk6;1pk4<1").
Proof. intros. unfold kimg_in_hull in *. apply Forall_app. auto. Qed.
#[using="HULL_ok argH_high"] Lemma hid_hull : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "M'Y='S6'QL'_2yR0%211'H'7&XMv0&_3r1%2281%5241(D%93821&X:r5r4r3r2%544321(9%A3@21p091pg@D1pl4H1phNJ1pR<L1").
Proof.
intros E cs model a Hh. unfold hid, vis. rewrite Hh. cbn [orb].
destruct (argH E a) eqn:Ha; [|reflexivity]. exfalso.
pose proof (argH_high _ _ Ha). unfold in_hull in Hh. apply andb_prop in Hh as [_ Hh]. apply Z.ltb_lt in Hh.
pose proof HULL_ok as HU; unfold hull_ok in HU; destruct HU as (?&?&?&?). unfold CEIL, KHI in *. lia.
Qed.
#[using="Type"] Lemma rdn_visible : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "QI'_2yR0%211'7p021'@y8%711%311p071'='<%115&RBvZJr5%3221'H%=16&Z@&RFr6%2217r4r3%64;321(4r2%22@1%<3;41'G&[3&_3%12Q0<r1%32Q21%5231&[4&[1&[7%11I%3281%5271%=271r9%11B(9%N3Q<21p051po>Q?1p0E1p0Q31ph4Q81po4Q;1pg@QD1pRFQ>1pRJQD1").
Proof.
intros H FULL a w. revert a. induction w as [|w IH]; intros a bs HH Hr x Hx; [lia|].
cbn [rdn] in Hr. unfold mrestrict in Hr at 1.
destruct (H a) eqn:Ha.
-
assert (Hs : seg_rom SEGS a = None).
{ unfold seg_rom. rewrite (memory_read1_hidden SEGS H HH a Ha). reflexivity. }
rewrite Hs in Hr. discriminate.
- destruct (Z.eq_dec (bv_unsigned x) (bv_unsigned a)) as [Heq|Hne].
+ assert (x = a) by (apply bv_eq; exact Heq). subst x. exact Ha.
+ fold (mrestrict H FULL) in Hr.
destruct (match FULL a with Some b => Some b | None => seg_rom SEGS a end) as [b|]; [|discriminate].
destruct (rdn SEGS (mrestrict H FULL) (a + 1)%bv w) as [rest|] eqn:Hr2; [|discriminate].
pose proof (u64_range x).
assert (Hu1 : bv_unsigned (a + 1)%bv = bv_unsigned a + 1) by (apply u_add1; lia).
eapply (IH (a + 1)%bv rest HH Hr2). rewrite Hu1. lia.
Qed.
#[using="Type"] Lemma know_ok_unhide : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "QO'Y='_2yR0%211'7p021'@y8%711%311p071'<'YE%211&RBvZJr4%3221&XAr2%211'Hr6r1%211(D%53F21r8%119%83I14p041pg@L1&XMv0&_3%12Q1<%4231%@3Q11<r9%11D(9%D3Q521p051pg@Q81&Z6&RF%12CHr5%44Q1:21r:r7%62H1%84Q531Np051p0;1p0H1p0Q41p0Q81pk0Q=1pRFQA1pRNQG1pRLQH1pR<QN1").
Proof.
intros E H1 H2 FULL k HH1 Hki Hsub Hhull HK.
assert (AG : forall a, H1 a = false -> mrestrict H2 FULL a = mrestrict H1 FULL a).
{ intros a Ha. unfold mrestrict. rewrite Ha. destruct (H2 a) eqn:Ha2; [|reflexivity].
rewrite (Hsub a Ha2) in Ha. discriminate. }
assert (GR : mem_grows (mrestrict H1 FULL) (mrestrict H2 FULL)).
{ intros x Hx. unfold mrestrict in *. destruct (H1 x) eqn:H1x; [exfalso; apply Hx; reflexivity|].
destruct (H2 x) eqn:H2x; [rewrite (Hsub x H2x) in H1x; discriminate | exact Hx]. }
unfold know_ok in *. apply Forall_forall. intros K Hin.
pose proof (proj1 (Forall_forall _ _) HK K Hin) as HKK.
pose proof (proj1 (Forall_forall _ _) Hki K Hin) as HKi.
destruct K as [a w v|a n|a n kb|lo hi|e m|e lo hi|a n|a1 n1 a2 n2|a n fc|a n]; cbn [kentry_ok] in *; try exact HKK.
7: { destruct HKK as [Hfl Hz]. split; [exact Hfl|]. intros i Hi.
pose proof (Hz i Hi) as Hzi. rewrite AG; [exact Hzi|].
unfold mrestrict in Hzi |- *. destruct (H1 _); [exfalso; apply Hzi; reflexivity | reflexivity]. }
- destruct HKK as (Hw & Hfl & Hrd). split; [exact Hw|]. split; [exact Hfl|].
rewrite <- Hrd. apply rdn_ext.
+ rewrite (flat_u E _ _ Hfl). destruct Hfl as (?&?&?&?). lia.
+ intros x Hx. apply AG. eapply rdn_visible; [exact HH1 | exact Hrd | exact Hx].
- destruct HKK as [Hfl Hz]. split; [exact Hfl|]. intros i Hi.
pose proof (Hz i Hi) as Hzi. rewrite AG; [exact Hzi|].
unfold mrestrict in Hzi. destruct (H1 _); [discriminate | reflexivity].
- destruct HKK as (Hfl & Hlen & Hz). split; [exact Hfl|]. split; [exact Hlen|]. intros i Hi.
pose proof (Hz i Hi) as Hzi. rewrite AG; [exact Hzi|].
unfold mrestrict in Hzi. destruct (H1 _); [discriminate | reflexivity].
- destruct HKK as (HA & HB & HC). split; [exact HA|]. split; [exact HB|]. intros i Hi.
assert (Hh : in_hull A (bv_unsigned (Z_to_bv 64 i)) = true).
{ unfold in_hull. rewrite u64_lit by lia. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
rewrite AG; [apply HC; exact Hi | apply Hhull; exact Hh].
- destruct HKK as [Hfl Hs]. split; [exact Hfl|]. intros d m Hd Hdm.
eapply store_ok_mono; [exact GR | apply Hs; assumption].
- destruct HKK as [Hfl Hz]. split; [exact Hfl|]. intros i Hi.
pose proof (Hz i Hi) as Hzi. rewrite AG; [exact Hzi|].
unfold mrestrict in Hzi. destruct (H1 _); [discriminate | reflexivity].
Qed.
#[using="Type"] Lemma vis_mono : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "Q4'Y='S6'QL'_2yR0%211'Q3'H'7&X=r6r5r1%43321(D%83721r7r2%93271%<3;15p051poF?1&XKr3%24>=17%B3A1;r4%54;@14%E3D1>p041p091pg@J1pl4N1pi0Q01phNQ11pR<Q31").
Proof.
intros E cs cs' model a Hm H. unfold vis in *.
apply orb_true_iff in H. apply orb_true_iff. destruct H as [H|H]; [left; exact H|]. right.
apply andb_true_iff in H as [H1 H2]. apply andb_true_iff. split; [exact H1|].
apply orb_true_iff in H2. apply orb_true_iff. destruct H2 as [H2|H2]; [left; exact H2|]. right. apply Hm. exact H2.
Qed.
#[using="Type"] Lemma in_allow_cons : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "QL'Y='S6'B'Y@%2211'Z0'Q3'<%114'S8'7'T?%511'H&X=r?r>r1%43321(D%73:21r@(RJr=&S3%11:r<r;r:(8&S5%11@%33L@1r9r8r7r6r5r4r3%B=A?>=<87654321r2%L3E21%N3Q11Hp0H1poFQ71pj>Q21pj@Q31pnBQ61piLQ81ph2Q?1pgBQ=1pj6Q<1piFQ?1poDQ@1pnFQA1pn0QC1pm8QE1phNQI1pR<QK1").
Proof.
intros. unfold in_allow, in_vis, in_sh in *. cbn [a_vis existsb].
apply orb_true_iff in H. apply orb_true_iff.
destruct H as [H|H]; [left|right]; apply orb_true_iff; right; exact H.
Qed.
#[using="Type"] Lemma hid_cons_sub : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "R2'Y='S6'B'Y@%2211'QL'_2yR0%211'Z0'Q3'<%118'S8'7'T?%511'H&X:r@(RJr;&S3r?%211r:r9r8(8r>&S5%118%43L31r7r6r5r4r3r2r1%D=C@?>=87654321r=r<%I4H321(D%L3O21rA%M41LB6%O3Q214p041pj>Q21pj@Q31pnBQ61piLQ81ph2QC1pgBQ=1pj6Q<1piFQ?1poDQ@1pnFQA1pn0QC1pg@QE1pl4QI1pm8QK1phNQO1pR<R11").
Proof.
intros E cs p model a ss tot ylo eg gh ab brk fd tid hna hlz H. unfold hid in *.
apply orb_true_iff in H. apply orb_true_iff. destruct H as [H|H]; [left; exact H|]. right.
apply negb_true_iff in H. apply negb_true_iff.
destruct (vis E cs model a) eqn:Hv; [|reflexivity].
rewrite (vis_mono E cs _ model a (fun z Hz => in_allow_cons E cs p ss tot ylo eg gh ab brk fd tid hna hlz z Hz) Hv) in H. discriminate.
Qed.
#[using="Type"] Lemma A_bytes_app : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "C'<'B'Q3%2211%411'H&R@&6r2r1%33721%511&[1%715%815%3221%;3>51pkB=1pk@>1").
Proof. intros l1 l2. induction l1; cbn [A_bytes app]; [lia|]. rewrite IHl1. lia. Qed.
#[using="Type"] Lemma page_allowedb_app_r : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "J'<'B'Q3%2211%411'_2yR0%211'H'7&RHr2r1%3221(D%73621&6r4r3%33@21%:219%=3<17p071pm8@1pkBD1pk@E1").
Proof. intros. unfold page_allowedb in *. rewrite existsb_app, H. apply orb_true_r. Qed.
#[using="Type"] Lemma MInv_app : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "Q2'<'B'Q3%2211%411'QL'RCr2r1%3221&[3&[1&RD%116&R@&6r4r3%33?21%511%9271&R4&R0%11@%311%?251r5%<3H1;%F21;p041p0E1pkJJ1pkBL1pk@M1").
Proof.
intros l1 l2 m [N1 N2 N3 N4 N5] Hb. constructor; try assumption.
intros p Hp. apply page_allowedb_app_r. apply N3. exact Hp.
Qed.
#[using="Type"] Lemma in_ivs_true : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "Q:'Q3'<'B'_2yR0%211%4211%611&J'H'7&XNr2r1%3221(D%73621'I'G&ZK%13>78&[3&_3&:%13CC;%32E1r3%6221&[4&[1&C%13JJB%:2L1%4281%6281%A281%B2@1qjHO1%E2Q01%O2G1pk<Q11poFQ91").
Proof.
intros z l. unfold in_ivs. rewrite existsb_exists. split.
- intros [iv [Hin Hb]]. apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. eauto.
- intros [iv [Hin Hb]]. exists iv. split; [exact Hin|]. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.
Section SE.
Local Abbreviation SEC_T_split_lit_denot := (ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "Q2'Y='Y@'Q3'H'B%1243&YNr3%211(Ar2r1%34;:21%:3851'_2yR0%211&Y<r5r4%3221&_1&[1&_3%726A%22:1%421@%62<1%I3<81p0@1pk0L1pgFN1pi@O1pR<Q11")) (only parsing).
Variable E : ltac:(sec_ty2 constr:(SEC_T_split_lit_denot) 0%nat 0%nat).
Lemma split_lit_denot : ltac:(sec_stmt2 constr:(SEC_T_split_lit_denot) 1%nat 0%nat).
Proof using Type E.
intros e b k H.
assert (G : forall e' : expr, edenot E e' = Z_to_bv 64 (bv_unsigned (edenot E e') + 0)).
{ intros e'. rewrite Z.add_0_r. symmetry. apply Z_to_bv_bv_unsigned. }
unfold split_lit in H.
destruct e; try (injection H as <- <-; apply G).
- injection H as <- <-. cbn [edenot]. rewrite u64_lit by (unfold two64; lia). rewrite Z.add_0_l. reflexivity.
- lazymatch type of H with (match ?o with _ => _ end = _) => destruct o end; try (injection H as <- <-; apply G).
lazymatch type of H with (match ?y with _ => _ end = _) => destruct y end; try (injection H as <- <-; apply G).
injection H as <- <-. cbn [edenot]. rewrite alu_add. unfold v_add. apply bv_eq.
rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. rewrite Z.add_mod_idemp_r by lia. reflexivity.
Qed.
End SE.
#[using="Type"] Lemma flat_x_sound : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "QL'Y='_2yR0%211'@y8%511%311p051'<'YE%211'Y@'Q3&Z6vZJr6r5r4%544321'H'7&T7r3r2%348721(D%73621'G&[3z&Z4r8(Y8%12A@%4231%7261&[1&_3&Y<%128A%32Q71%5271&[9+2+R0%3221%B251&[4%12C8%F231%G2?1p0I1p0Q21pl:Q:1pm6Q:1pgFQ<1pk0Q>1pTDQB1pR<QK1").
Proof.
intros E M k b off n HK H. unfold flat_x in H.
destruct (base_range k b) as [[lo hi]|] eqn:Hb; [|discriminate].
destruct (xlo k n) as [nl|] eqn:Hnl; [|discriminate]. destruct (xhi k n) as [nh|] eqn:Hnh; [|discriminate].
apply andb_prop in H as [H Hn]. apply andb_prop in H as [H1 H2].
apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.ltb_lt in Hn. unfold two64 in H2.
pose proof (base_range_sound SEGS E M k b lo hi HK Hb). pose proof (xlo_sound SEGS E M k n nl HK Hnl). pose proof (xhi_sound SEGS E M k n nh HK Hnh).
unfold estart. cbn [a_base a_off]. lia.
Qed.
#[using="Type"] Lemma u_of_split : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "Q>'Y='Y@'Q3'H'B%1243&YNr3%211(Ar2r1%34;:21%:3851'G&[3z&Z4r5(Y8%12=:%4231%7261&[4&[9+2+R0%3221%5271%?271&_3yR0&Y<r6%221@%5241r4%B21N%E251%Q43Q541p0;1p0L1pk0Q81pgFQ:1pi@Q;1pR<Q=1").
Proof.
intros E e b k Hs Hr. rewrite (split_lit_denot E e b k Hs). unfold estart in *. cbn [a_base a_off] in *.
apply u64_lit. lia.
Qed.
#[using="HS XN XE XB KC"] Lemma pageup_pagedown_gap : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "D'Q3&[3r2r1%3221&[:&Y0%115&XOr3%211%6241&[1%82;4+WoN%3221%?251p0=1pgFB1pg@C1").
Proof.
intros a b H. unfold pageup, pagedown.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.
#[using="nx0 HS XN XE XB"] Lemma maps_match_exact : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "Q0'Y='<'S<%211'B'_2yR0%211%4211%811'H'7&V3r2%211(D%63521&J&XDr4r3%33218&Q1&X3%115%34GA15%@3A=1%:261p0<1pk<D1pl8K1pR<O1").
Proof.
intros E ms. induction ms as [|m ms IH]; intros l Hnf; cbn [maps_match map].
- tauto.
- cbn [no_fog forallb] in Hnf. apply andb_prop in Hnf as [Hm Hr]. apply negb_true_iff in Hm. rewrite Hm.
split.
+ intros (l' & -> & Hm'). f_equal. apply (proj1 (IH l' Hr)). exact Hm'.
+ intros ->. exists (map (amap_den E) ms). split; [reflexivity|]. apply (proj2 (IH _ Hr)). reflexivity.
Qed.
#[using="Type"] Lemma maps_match_In : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "Q3'Y='<'S<%211'B'_2yR0%211%4211%811&XDr4r3r2%43321&ZK%13>35'H'7&TJ%118(9%53421&X3r7%221>r5%<3C21p061p0=1p0@1pkJM1pk<G1pl8N1pR<Q21").
Proof.
intros E ms. induction ms as [|m0 ms IH]; intros l m HM Hin Hf; [destruct Hin|].
cbn [maps_match] in HM. destruct Hin as [<-|Hin].
- rewrite Hf in HM. destruct HM as (l' & -> & _). left. reflexivity.
- destruct (is_fog m0).
+ destruct HM as [HM|(iv & l' & -> & _ & HM)]; [exact (IH _ _ HM Hin Hf) | right; exact (IH _ _ HM Hin Hf)].
+ destruct HM as (l' & -> & HM). right. exact (IH _ _ HM Hin Hf).
Qed.
#[using="Type"] Lemma in_ivs_maps_match : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "QI'Y='<'S<%211'B'_2yR0%211%4211%811'Q3&XDr5r4r3%43321&ZK%13?35'H'7&TJ%118(9%53421'G&[3&_3&Y<r8&S:%11B%4231%62J1%821D&[4&[1&S;%11I%;2:1%=2Q11%5281%72L1%B291&XNr7%22Q11(D%M3L21p061p0J1p0Q11p0Q41poFQ:1pkJQC1pk<Q=1pl8QD1pR<QH1").
Proof.
intros E ms l m z HM Hin Hf Hz. apply (proj2 (in_ivs_true z _)). exists (amap_den E m).
split; [exact (maps_match_In E ms l m HM Hin Hf) | exact Hz].
Qed.
#[using="Type"] Lemma maps_match_cons : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "Q>'Y='<'S<%211'B'_2yR0%211%4211%811'Y@'UO'H'7&TLr1%211(9%63521&XDr7r6r5%43321r8(8(RKr4r3%33721%53L1:(A&Y<%129;%22:7%44LL21%;3L1?%B3=71p0?1p0E1pk0M1pl:O1pgFQ01pk<Q21pl8Q91pR<Q=1").
Proof.
intros E ms l b n k Hk HM. cbn [maps_match]. unfold is_fog. cbn [am_kind]. rewrite Hk. exists l. split; [reflexivity | exact HM].
Qed.
#[using="Type"] Lemma maps_match_length : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "H'Y='<'S<%211'B'_2yR0%211%4211%811&XDr3r2r1%43321'N&;%1295%22@7%4221p061pk<<1pl8C1pR<G1").
Proof.
intros E ms. induction ms as [|m ms IH]; intros l HM; cbn [maps_match] in HM.
- subst l. cbn. lia.
- cbn [length]. destruct (is_fog m).
+ destruct HM as [HM|(iv & l' & -> & _ & HM)]; [pose proof (IH _ HM); lia | cbn; pose proof (IH _ HM); lia].
+ destruct HM as (l' & -> & HM). cbn. pose proof (IH _ HM). lia.
Qed.
#[using="Type"] Lemma maps_match_elem : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "QI'Y='<'S<%211'B'_2yR0%211%4211%811&XDr4r3r2%43321&ZK%13834'I'Gr1r6%63C21'L'H'7&TJ%117(9%53421&X3r7%221<%93HE1%?251(D%<3;91&[3&_3&C%13Q0Q0L%32Q21&Y1&S;%11H%32>1%9251%L2;1%I2>1%N2K1qkJQ?1%Q12Q@1p0Q31p0Q61pjHQ=1pk<Q=1pl8QD1pR<QH1").
Proof.
intros E ms. induction ms as [|m ms IH]; intros l iv HM Hin; cbn [maps_match] in HM.
- subst l. destruct Hin.
- destruct (is_fog m) eqn:Hf.
+ destruct HM as [HM|(iv0 & l' & -> & Hsz & HM)].
* destruct (IH _ _ HM Hin) as (m' & Hm' & H'). exists m'. split; [right; exact Hm' | exact H'].
* destruct Hin as [<-|Hin].
-- exists m. split; [left; reflexivity|]. right. split; [exact Hf | exact Hsz].
-- destruct (IH _ _ HM Hin) as (m' & Hm' & H'). exists m'. split; [right; exact Hm' | exact H'].
+ destruct HM as (l' & -> & HM). destruct Hin as [<-|Hin].
* exists m. split; [left; reflexivity|]. left. split; [exact Hf | reflexivity].
* destruct (IH _ _ HM Hin) as (m' & Hm' & H'). exists m'. split; [right; exact Hm' | exact H'].
Qed.
#[using="Type"] Lemma maps_match_rekind : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "Q@'Y='<'S<%211'B'_2yR0%211%4211%811p088'G'H'Y@&S:r2r1%211%411%513%83721&S;%115%217%<3;21'7&TJ%11:%21<%A3421%C261%D2;1pkJN1&XDr5r4r3%43321r6&Q1%14Q6Q646%83316p051p0;1piJQ21pk<Q41pl8Q;1pR<Q?1").
Proof.
intros E ms. induction ms as [|m ms IH]; intros l f Hf HM; cbn [maps_match map] in *; [exact HM|].
destruct (Hf m) as (Hb & Hn & Hk). rewrite Hk. unfold uE, amap_den in *. rewrite Hb, Hn.
destruct (is_fog m).
- destruct HM as [HM|(iv & l' & -> & Hsz & HM)]; [left; exact (IH _ f Hf HM) | right].
exists iv, l'. split; [reflexivity|]. split; [exact Hsz | exact (IH _ f Hf HM)].
- destruct HM as (l' & -> & HM). exists l'. split; [reflexivity | exact (IH _ f Hf HM)].
Qed.
#[using="Type"] Lemma filter_all_true : forall {T} (f : T -> bool) l, (forall x, In x l -> f x = true) -> List.filter f l = l.
Proof.
intros T f l H. induction l as [|x l IH]; [reflexivity|]. cbn. rewrite (H x (or_introl eq_refl)).
rewrite IH by (intros y Hy; apply H; right; exact Hy). reflexivity.
Qed.
#[using="Type"] Lemma aluop_eqb_refl' : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "9'R6'H'7&Y:r1%2211(D%63521plL81").
Proof. intros []; reflexivity. Qed.
#[using="Type"] Lemma mulop_eqb_refl' : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "9'R7'H'7&YGr1%2211(D%63521plL81").
Proof. intros []; reflexivity. Qed.
#[using="Type"] Lemma expr_eqb_refl' : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "9'Y@'H'7&YAr1%2211(D%63521pi@81").
Proof.
induction e; cbn; rewrite ?aluop_eqb_refl', ?mulop_eqb_refl', ?IHe1, ?IHe2, ?IHe, ?Z.eqb_refl, ?Nat.eqb_refl, ?Bool.eqb_reflx; reflexivity.
Qed.
#[using="Type"] Lemma amap_eqb_refl' : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "9'S<'H'7&S=r1%2211(D%63521pkJ81").
Proof. intros [b l k]. unfold amap_eqb. cbn. rewrite !expr_eqb_refl'. destruct k; reflexivity. Qed.
#[using="Type"] Lemma map_remove_notin' : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "L'<'B'_2yR0%211%4211%611&ZK(Ar2r1%347721r4%63821&K'Hr3%23=15%411p061pn>@1pgFA1&R1%127>%93B18p041pg@F1pk<E1").
Proof.
induction l as [|[b sz] l IH]; intros a H; [reflexivity|].
unfold map_remove in *. cbn [List.filter fst]. rewrite (bv_eqb_neq b a) by (apply (H b sz); left; reflexivity). cbn [negb].
f_equal. apply IH. intros b' s' Hin. apply (H b' s'). right. exact Hin.
Qed.
Section SE.
Local Abbreviation SEC_T_maps_match_remove := (ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "R4'Y='<'S<%211'B'_2yR0%211%4211%811&XDr4r3r2%43321&ZK%13>35'H'7&TJ%118(9%53421'ZLr5%22A1r1r7%=3D21&:%13GGA&Y<r:&S:%117%4231%C3M61&X3r;r8%3221%H3Q1M1p061p0?1pjHQ41r9&ZM&>&S=%12GF%311qkLQA1%63QB1=&R1r6%F11%I2;1%42N1%Q@3=61p0?1p0Q31p0Q71p0Q>1p0QA1pkJQN1pk<QH1pl8QO1pR<R31")) (only parsing).
Variable E : ltac:(sec_ty2 constr:(SEC_T_maps_match_remove) 0%nat 0%nat).
Lemma maps_match_remove : ltac:(sec_stmt2 constr:(SEC_T_maps_match_remove) 1%nat 0%nat).
Proof using Type E.
intros ms.
induction ms as [|m0 ms IH]; intros l m HM Hin Hf Hnd Huniq; [destruct Hin|].
cbn [maps_match] in HM. cbn [List.filter].
destruct (amap_eqb m0 m) eqn:Heq.
-
apply amap_eqb_eq in Heq. subst m0.
rewrite Hf in HM. destruct HM as (l' & -> & HM). cbn [negb].
unfold map_remove. cbn [List.filter amap_den fst]. rewrite bv_eqb_refl. cbn [negb].
inversion Hnd as [|x l0 Hnotin Hnd']; subst.
assert (Hnotin' : ~ In m ms).
{ intros Hm. apply Hnotin. exact (maps_match_In E ms l' m HM Hm Hf). }
rewrite (filter_all_true (fun m' => negb (amap_eqb m' m)) ms).
2:{ intros x Hx. destruct (amap_eqb x m) eqn:Ex; [|reflexivity]. apply amap_eqb_eq in Ex. subst x. exfalso. exact (Hnotin' Hx). }
fold (map_remove l' (edenot E (am_base m))). rewrite map_remove_notin'; [exact HM|].
intros b sz Hbs Hb. apply Hnotin. rewrite <- (Huniq (b, sz) (or_intror Hbs) Hb). exact Hbs.
-
destruct Hin as [->|Hin]; [rewrite amap_eqb_refl' in Heq; discriminate|].
cbn [negb maps_match].
destruct (is_fog m0) eqn:Hf0.
+ destruct HM as [HM|(iv & l' & -> & Hsz & HM)].
* left. exact (IH _ _ HM Hin Hf Hnd Huniq).
* inversion Hnd as [|x l0 Hnotin Hnd']; subst.
assert (Hne : bv_eqb (fst iv) (edenot E (am_base m)) = false).
{ apply bv_eqb_neq. intros Hb. apply Hnotin. rewrite (Huniq iv (or_introl eq_refl) Hb).
exact (maps_match_In E ms l' m HM Hin Hf). }
unfold map_remove. cbn [List.filter]. rewrite Hne. cbn [negb]. fold (map_remove l' (edenot E (am_base m))).
right. exists iv, (map_remove l' (edenot E (am_base m))). split; [reflexivity|]. split; [exact Hsz|].
apply (IH _ _ HM Hin Hf Hnd'). intros x Hx. apply Huniq. right. exact Hx.
+ destruct HM as (l' & -> & HM).
inversion Hnd as [|x l0 Hnotin Hnd']; subst.
assert (Hne : bv_eqb (fst (amap_den E m0)) (edenot E (am_base m)) = false).
{ apply bv_eqb_neq. intros Hb. apply Hnotin. rewrite (Huniq _ (or_introl eq_refl) Hb).
exact (maps_match_In E ms l' m HM Hin Hf). }
unfold map_remove. cbn [List.filter]. rewrite Hne. cbn [negb]. fold (map_remove l' (edenot E (am_base m))).
exists (map_remove l' (edenot E (am_base m))). split; [reflexivity|].
apply (IH _ _ HM Hin Hf Hnd'). intros x Hx. apply Huniq. right. exact Hx.
Qed.
End SE.
#[using="Type"] Lemma in_ivs_map_den : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "QB'Y='<'S<%211'Q3&ZKr2r3%33621'G&[3&_3yR0&Y<r5&S:%119%4231%7261%921=&[4&[1&S;%11@%;2:1%>2=1%5281%72E1%C291'H'7&XN&Q1'B'_2%11G%3211&X3r6%211%84Q641J%:2Q21(D%>3=21p0@1p0Q51poFQ:1pkJQ=1pl8Q=1pR<QA1").
Proof.
intros E ms m z Hin Hz. apply (proj2 (in_ivs_true z _)). exists (amap_den E m). split; [apply in_map; exact Hin | exact Hz].
Qed.
#[using="Type"] Lemma existsb_false_forall : forall {T} (f : T -> bool) l, (forall x, In x l -> f x = false) -> existsb f l = false.
Proof.
intros T f l H. induction l as [|x l IH]; [reflexivity|]. cbn [existsb].
rewrite (H x (or_introl eq_refl)). cbn [orb]. apply IH. intros y Hy. apply H. right. exact Hy.
Qed.
Section SE.
Local Abbreviation SEC_T_shadow_facts_holder := (forall E M k ms b n sb sk, know_ok SEGS E M k ->
split_lit (eadd (mkSrl k b 3) (ELit (shadow_off A))) = (sb, sk) ->
(match find_containing k ms [KRWLAZY] sb sk (mkSrl k n 3) with Some _ => true | None => false end
|| shadow_band A k ms b n sb sk (mkSrl k n 3))%bool = true ->
(0 <= bv_unsigned (edenot E sb) + sk < 2 ^ 64 -> bv_unsigned (edenot E sb) + sk = shadow_off A + bv_unsigned (edenot E b) / 8)
/\ exists m, In m ms /\ is_fog m = false /\ am_kind m = KRWLAZY
/\ bv_unsigned (edenot E (am_base m)) <= bv_unsigned (edenot E sb) + sk
/\ bv_unsigned (edenot E sb) + sk + bv_unsigned (edenot E (mkSrl k n 3))
<= bv_unsigned (edenot E (am_base m)) + bv_unsigned (edenot E (am_len m))) (only parsing).
Variable E : ltac:(sec_ty2 constr:(SEC_T_shadow_facts_holder) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_shadow_facts_holder) 1%nat 0%nat).
Variable k : ltac:(sec_ty2 constr:(SEC_T_shadow_facts_holder) 2%nat 0%nat).
Variable ms : ltac:(sec_ty2 constr:(SEC_T_shadow_facts_holder) 3%nat 0%nat).
Variable b : ltac:(sec_ty2 constr:(SEC_T_shadow_facts_holder) 4%nat 0%nat).
Variable n : ltac:(sec_ty2 constr:(SEC_T_shadow_facts_holder) 5%nat 0%nat).
Variable sb : ltac:(sec_ty2 constr:(SEC_T_shadow_facts_holder) 6%nat 0%nat).
Variable sk : ltac:(sec_ty2 constr:(SEC_T_shadow_facts_holder) 7%nat 0%nat).
Lemma shadow_facts_holder : ltac:(sec_stmt2 constr:(SEC_T_shadow_facts_holder) 8%nat 0%nat).
Proof using HS XN XE XB SHADOW_ok KC E M k ms b n sb sk.
intros HK Hss Hjust.
assert (Usn : bv_unsigned (edenot E (mkSrl k n 3)) = bv_unsigned (edenot E n) / 8).
{ rewrite (mkSrl_denot SEGS E _ k n 3 (Z_to_bv 64 3) HK) by (rewrite u64_lit by lia; reflexivity).
rewrite u_srl64. rewrite u64_lit by lia. reflexivity. }
pose proof (u64_range (edenot E (mkSrl k n 3))) as Rsn.
pose proof SHADOW_ok as SO. unfold shadow_ok in SO. pose proof (u64_range (edenot E b)) as Rb. pose proof (u64_range (edenot E n)) as Rn.
assert (HS0raw : 0 <= bv_unsigned (edenot E sb) + sk < 2 ^ 64 -> bv_unsigned (edenot E sb) + sk = shadow_off A + bv_unsigned (edenot E b) / 8).
{ intros Hnw. pose proof (split_lit_denot E _ sb sk Hss) as D. unfold eadd in D. rewrite mkAlu_denot in D. cbn [edenot] in D.
apply (f_equal bv_unsigned) in D. rewrite u_add64 in D.
rewrite (mkSrl_denot SEGS E _ k b 3 (Z_to_bv 64 3) HK) in D by (rewrite u64_lit by lia; reflexivity).
rewrite u_srl64 in D.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
rewrite !u64_lit in D by (unfold CEIL in *; lia).
change (2 ^ (3 mod 64)) with 8 in D.
rewrite (Z.mod_small (bv_unsigned (edenot E b) / 8 + shadow_off A)) in D by (unfold CEIL, KHI in *; lia).
lia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
split; [exact HS0raw|].
apply orb_prop in Hjust as [Hf|Hband].
- destruct (find_containing k ms [KRWLAZY] sb sk (mkSrl k n 3)) as [m|] eqn:Hf'; [|discriminate].
unfold find_containing in Hf'. apply find_some in Hf' as [Hmin Hmb]. apply andb_prop in Hmb as [Hkind Hins].
apply andb_prop in Hkind as [Hnf Hkind]. apply negb_true_iff in Hnf.
cbn [existsb] in Hkind. rewrite orb_false_r in Hkind. apply mkind_eqb_eq in Hkind.
pose proof (xinside_sound SEGS E _ k sb sk (mkSrl k n 3) (am_base m) 0 (am_len m) HK Hins) as [I1 I2].
unfold estart, elenZ in I1, I2. cbn [a_base a_off] in I1, I2. rewrite Z.add_0_r in I1, I2.
exists m. repeat split; assumption.
- unfold shadow_band in Hband. apply andb_prop in Hband as [Hflsh Hband].
destruct (flat_x_sound E _ k sb sk (mkSrl k n 3) HK Hflsh) as (FS1 & FS2 & FS3).
unfold estart, elenZ in FS1, FS2, FS3. cbn [a_base a_off] in FS1, FS2, FS3.
pose proof (HS0raw ltac:(lia)) as HS0'.
destruct (xlo k b) as [blo|] eqn:Hblo; [|discriminate].
destruct (xhi k b) as [bhi|] eqn:Hbhi; [|discriminate].
destruct (xhi k n) as [nhi'|] eqn:Hnhi2; [|discriminate].
pose proof (xlo_sound SEGS E _ k b blo HK Hblo) as XL. pose proof (xhi_sound SEGS E _ k b bhi HK Hbhi) as XH.
pose proof (xhi_sound SEGS E _ k n nhi' HK Hnhi2) as XNh.
apply existsb_exists in Hband as (K & HKin & HKb).
destruct K as [| | | | | | |[e1 o1] n1 [b' o2] n'| |]; try discriminate HKb.
destruct e1 as [lo| | | | | | |]; try discriminate HKb. destruct o1; try discriminate HKb.
destruct n1 as [L| | | | | | |]; try discriminate HKb. destruct o2; try discriminate HKb.
apply andb_prop in HKb as [HKb HexH]. apply andb_prop in HKb as [HKb HexL]. apply andb_prop in HKb as [HKb HloL].
apply andb_prop in HKb as [HKb HL0]. apply andb_prop in HKb as [HKb Hlo0]. apply andb_prop in HKb as [Eb En].
apply expr_eqb_eq in Eb. apply expr_eqb_eq in En. subst b' n'.
apply Z.leb_le in Hlo0. apply Z.leb_le in HL0. apply Z.ltb_lt in HloL. unfold two64 in HloL.
pose proof (proj1 (Forall_forall _ _) HK _ HKin) as KD. cbn [kentry_ok] in KD.
unfold estart, elenZ in KD. cbn [a_base a_off edenot] in KD. rewrite !u64_lit in KD by lia. rewrite !Z.add_0_r in KD.
assert (PICK : forall m slo shi, In m ms -> lit_lazy_holds m slo shi = true ->
slo <= bv_unsigned (edenot E sb) + sk ->
bv_unsigned (edenot E sb) + sk + bv_unsigned (edenot E (mkSrl k n 3)) <= shi ->
exists m0, In m0 ms /\ is_fog m0 = false /\ am_kind m0 = KRWLAZY
/\ bv_unsigned (edenot E (am_base m0)) <= bv_unsigned (edenot E sb) + sk
/\ bv_unsigned (edenot E sb) + sk + bv_unsigned (edenot E (mkSrl k n 3))
<= bv_unsigned (edenot E (am_base m0)) + bv_unsigned (edenot E (am_len m0))).
{ intros m slo shi Hm Hh H1 H2. unfold lit_lazy_holds in Hh.
apply andb_prop in Hh as [Hh Hlit]. apply andb_prop in Hh as [Hnf Hk]. apply negb_true_iff in Hnf. apply mkind_eqb_eq in Hk.
destruct (am_base m) as [B| | | | | | |] eqn:HB; try discriminate Hlit. destruct (am_len m) as [L'| | | | | | |] eqn:HL; try discriminate Hlit.
apply andb_prop in Hlit as [Hlit H6]. apply andb_prop in Hlit as [Hlit H5]. apply andb_prop in Hlit as [Hlit H4].
apply andb_prop in Hlit as [H2' H3]. apply Z.leb_le in H2'. apply Z.ltb_lt in H3. apply Z.ltb_lt in H4. apply Z.leb_le in H5. apply Z.leb_le in H6.
unfold two64 in H4.
exists m. rewrite HB, HL. cbn [edenot]. rewrite !u64_lit by lia. repeat split; try assumption; lia. }
rewrite Usn in *. rewrite HS0' in *.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
destruct KD as [HIGH|LOW].
+
apply existsb_exists in HexH as (mH & HmH & HhH).
apply (PICK mH _ _ HmH HhH).
* apply Z.add_le_mono_l. apply Z.div_le_mono; lia.
* rewrite <- Z.add_assoc. apply Z.add_le_mono_l.
apply (Z.le_trans _ ((bv_unsigned (edenot E b) + bv_unsigned (edenot E n)) / 8)); [apply Z.div_le_lower_bound|apply Z.div_le_mono]; lia.
+
apply existsb_exists in HexL as (mL & HmL & HhL).
apply (PICK mL _ _ HmL HhL).
* apply Z.add_le_mono_l. apply Z.div_le_mono; lia.
* rewrite <- Z.add_assoc. apply Z.add_le_mono_l.
apply (Z.le_trans _ ((bv_unsigned (edenot E b) + bv_unsigned (edenot E n)) / 8)); [apply Z.div_le_lower_bound|apply Z.div_le_mono]; lia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_vis_add_sound := (ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "QJ'Y='S6'Y@'<'YE%211&R8y5'_2yR0%211%5241'@y8%611%311p061'QL'H%71B&WCv0vQEr8r7r6r5%76654321(4r4%22M1%=3<41'X4r:r9r3r2%5543821&Z6vZJr;&WM%142A7=%54431Cr<%=51EDC@p031p0:1p0A1pl4Q01pRFQ21pTNQ81pi4QC1pk0Q@1pl:QD1pgFQE1phNQG1pR<QI1")) (only parsing).
Variable E : ltac:(sec_ty2 constr:(SEC_T_vis_add_sound) 0%nat 0%nat).
Variable cs : ltac:(sec_ty2 constr:(SEC_T_vis_add_sound) 1%nat 0%nat).
Variable b : ltac:(sec_ty2 constr:(SEC_T_vis_add_sound) 2%nat 0%nat).
Variable n : ltac:(sec_ty2 constr:(SEC_T_vis_add_sound) 3%nat 0%nat).
Variable k : ltac:(sec_ty2 constr:(SEC_T_vis_add_sound) 4%nat 0%nat).
Variable cs2 : ltac:(sec_ty2 constr:(SEC_T_vis_add_sound) 5%nat 0%nat).
Variable R : ltac:(sec_ty2 constr:(SEC_T_vis_add_sound) 6%nat 0%nat).
Variable FULL : ltac:(sec_ty2 constr:(SEC_T_vis_add_sound) 7%nat 0%nat).
Variable model : ltac:(sec_ty2 constr:(SEC_T_vis_add_sound) 8%nat 0%nat).
Lemma vis_add_sound : ltac:(sec_stmt2 constr:(SEC_T_vis_add_sound) 9%nat 0%nat).
Proof using HS XN XE XB SHADOW_ok argH_high KC E cs b n k cs2 R FULL model.
intros Hv HC HKk.
rewrite vis_add_eq in Hv. unfold vis_add_ref in Hv.
destruct (split_lit b) as [bb bk] eqn:Hsplit.
destruct (shadow_of A (kn cs) b n) as [[sb sk] sn] eqn:Hsh.
destruct (xhi (kn cs) n) as [nhi|] eqn:Hnhi; [|discriminate].
match type of Hv with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
injection Hv as <-.
apply andb_prop in Hc as [Hc Hbudget]. apply andb_prop in Hc as [Hc Hapg]. apply andb_prop in Hc as [Hc Hapart]. apply andb_prop in Hc as [Hc Hvn].
apply andb_prop in Hc as [Hc Hvb]. apply andb_prop in Hc as [Hc Hflat]. apply andb_prop in Hc as [Halb Haln].
apply Z.leb_le in Hbudget.
pose proof (co_know _ _ _ _ _ HC) as HK.
pose proof (xhi_sound SEGS E _ (kn cs) n nhi HK Hnhi) as Hnhi'.
destruct (flat_x_sound E _ (kn cs) bb bk n HK Hflat) as (Fb1 & Fb2 & Fb3).
pose proof (u_of_split E b bb bk Hsplit ltac:(lia)) as Ub.
set (cs2 := ACS _ _ _ _ _ _ _ _ _ _ _ _ _).
assert (SUB : forall a, hid E cs2 model a = true -> hid E cs model a = true).
{ intros a. apply hid_cons_sub. }
assert (HA : allowA E cs2 = allow1 E (b, n) ++ allowA E cs) by reflexivity.
assert (Hcost : A_bytes (allow1 E (b, n)) <= vis_cost nhi).
{ unfold allow1, vis_cost. cbn [A_bytes fst snd]. unfold sh_lo, sh_hi. cbn [fst snd].
pose proof (u64_range (edenot E b)) as Rb. pose proof (u64_range (edenot E n)) as Rn. unfold uE in *.
pose proof (pageup_pagedown_gap (bv_unsigned (edenot E b)) (bv_unsigned (edenot E b) + bv_unsigned (edenot E n)) ltac:(lia)) as G1.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
pose proof (pageup_pagedown_gap (shadow_off A + bv_unsigned (edenot E b) / 8)
(shadow_off A + (bv_unsigned (edenot E b) + bv_unsigned (edenot E n)) / 8) ltac:(lia)) as G2.
assert (G3 : (bv_unsigned (edenot E b) + bv_unsigned (edenot E n)) / 8 - bv_unsigned (edenot E b) / 8 <= nhi / 8 + 1) by lia.
lia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
assert (HKsh : know_ok SEGS E (Mr E cs2 model FULL) (shadow_facts A (kn cs) (a_maps cs) b n)).
{ unfold shadow_facts. rewrite Hsh.
match goal with |- know_ok _ _ _ (if ?c then _ else _) => destruct c eqn:Hjust; [|constructor] end.
unfold shadow_of in Hsh.
destruct (split_lit (eadd (mkSrl (kn cs) b 3) (ELit (shadow_off A)))) as [sb' sk'] eqn:Hss. injection Hsh as -> -> <-.
assert (Usn : elenZ E (mkSrl (kn cs) n 3) = bv_unsigned (edenot E n) / 8).
{ unfold elenZ. rewrite (mkSrl_denot SEGS E _ (kn cs) n 3 (Z_to_bv 64 3) HK) by (rewrite u64_lit by lia; reflexivity).
rewrite u_srl64. rewrite u64_lit by lia. reflexivity. }
pose proof (u64_range (edenot E (mkSrl (kn cs) n 3))) as Rsn.
pose proof SHADOW_ok as SO. unfold shadow_ok in SO. pose proof (u64_range (edenot E b)) as Rb.
pose proof (co_isp _ _ _ _ _ HC) as [_ ISP]. unfold sp_window_lo, sp_window_hi in ISP.
destruct (shadow_facts_holder E _ (kn cs) (a_maps cs) b n sb sk HK Hss Hjust) as (HS0raw & m & Hmin & Hnf & Hkind & I1 & I2).
assert (Hmv : In (amap_den E m) (vm_maps (m_vmmaps model))) by (eapply maps_match_In; [exact (co_maps _ _ _ _ _ HC) | exact Hmin | exact Hnf]).
pose proof (proj1 (Forall_forall _ _) (co_bounds _ _ _ _ _ HC) _ Hmv) as (B1 & B2 & B3 & B4 & B5). cbn [amap_den fst snd] in B1, B2, B3, B4, B5.
pose proof (utop_bounds E) as UB.
pose proof (u64_range (edenot E (am_base m))) as Rmb.
set (S0 := estart E (SA sb sk)) in *.
assert (ES0 : S0 = bv_unsigned (edenot E sb) + sk) by reflexivity.
assert (HS0 : S0 = shadow_off A + bv_unsigned (edenot E b) / 8) by (rewrite ES0; apply HS0raw; lia).
assert (BYTE : forall i, 0 <= i < elenZ E (mkSrl (kn cs) n 3) ->
Mr E cs2 model FULL (Z_to_bv 64 (S0 + i)) = Some (Z_to_bv 8 0)).
{ intros i Hi. rewrite Usn in Hi.
set (z := S0 + i).
assert (Hz : 0 <= z < 2 ^ 64).
{ unfold z. rewrite ES0. pose proof Usn as U2. unfold elenZ in U2. clear - Hi I1 I2 B5 UB ISP Rsn Rmb Rb U2.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
lia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
assert (Zin : bv_unsigned (edenot E (am_base m)) <= z < bv_unsigned (edenot E (am_base m)) + bv_unsigned (edenot E (am_len m))
/\ z < utop E /\ (z < img_lo A \/ img_hi A <= z) /\ S0 <= z < S0 + bv_unsigned (edenot E n) / 8).
{ unfold z. rewrite ES0. pose proof Usn as U2. unfold elenZ in U2. clear - Hi I1 I2 B4 B5 UB Rsn Rmb Rb U2.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
lia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
clearbody z. destruct Zin as (Z1 & Z2 & Z3 & Z4).
set (a := Z_to_bv 64 z). assert (Ua : bv_unsigned a = z) by (unfold a; apply u64_lit; exact Hz).
assert (Hm1 : in_ivs (bv_unsigned a) (vm_maps (m_vmmaps model)) = true).
{ eapply in_ivs_maps_match; [exact (co_maps _ _ _ _ _ HC) | exact Hmin | exact Hnf |]. rewrite Ua. exact Z1. }
destruct (proj1 (Forall_forall _ _) (co_kinds _ _ _ _ _ HC) m Hmin Hkind a ltac:(rewrite Ua; exact Z1)) as [Hna Hlz].
assert (Hargh : argH E a = false).
{ destruct (argH E a) eqn:Ha; [|reflexivity]. pose proof (argH_high _ _ Ha). pose proof (utop_bounds E). lia. }
assert (Hvis2 : hid E cs2 model a = false).
{ unfold hid. rewrite Hargh. cbn [orb]. apply negb_false_iff. unfold vis.
rewrite Hm1, Hna, Hlz. cbn [negb andb].
assert (Hsh2 : in_sh E cs2 (bv_unsigned a) = true).
{ unfold in_sh. cbn [cs2 a_vis existsb]. unfold sh_lo, sh_hi. cbn [fst snd]. unfold uE.
rewrite Ua. apply orb_true_iff. left. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt].
- lia.
- Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
unfold in_allow. rewrite Hsh2. rewrite !orb_true_r. reflexivity. }
assert (Hhid1 : hid E cs model a = true).
{ unfold hid. rewrite Hargh. cbn [orb]. apply negb_true_iff. unfold vis.
rewrite Hm1, Hna, Hlz. cbn [negb andb].
assert (Hh : in_hull A (bv_unsigned a) = false).
{ unfold in_hull. rewrite Ua. apply andb_false_iff. destruct Z3 as [Z3|Z3]; [left; apply Z.leb_gt | right; apply Z.ltb_ge]; lia. }
assert (Hc : (utop E <=? bv_unsigned a) = false) by (apply Z.leb_gt; rewrite Ua; lia).
rewrite Hh, Hc. cbn [orb].
assert (Hold : in_allow E cs (bv_unsigned a) = false).
{ unfold in_allow. apply orb_false_iff.
assert (P : forall p, In p (a_vis cs) ->
((uE E (fst p) <=? bv_unsigned a) && (bv_unsigned a <? uE E (fst p) + uE E (snd p)))%bool = false
/\ ((sh_lo E p <=? bv_unsigned a) && (bv_unsigned a <? sh_hi E p))%bool = false).
{ intros p Hp. pose proof (proj1 (forallb_forall _ _) Hapart p Hp) as Hpp. cbv beta in Hpp.
destruct (split_lit (fst p)) as [pb pk] eqn:Hps.
apply andb_prop in Hpp as [Hpp Hap2]. apply andb_prop in Hpp as [Hpf Hap1].
destruct (flat_x_sound E _ (kn cs) pb pk (snd p) HK Hpf) as (Fp1 & Fp2 & Fp3).
pose proof (u_of_split E (fst p) pb pk Hps ltac:(lia)) as Up.
pose proof (ranges_apart_x_sound SEGS E _ (kn cs) _ _ _ _ _ _ HK Hap1) as A1.
pose proof (ranges_apart_x_sound SEGS E _ (kn cs) _ _ _ _ _ _ HK Hap2) as A2.
fold S0 in A2. unfold elenZ in A1, A2. rewrite Usn in A2 |- * || idtac.
change (elenZ E (mkSrl (kn cs) n 3)) with (bv_unsigned (edenot E (mkSrl (kn cs) n 3))) in Hi |- * || idtac.
unfold sh_lo, sh_hi, uE. rewrite Up, Ua. rewrite <- Ub in A1.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
pose proof Usn as U'. unfold elenZ in U'. rewrite ?U' in A2.
split; apply andb_false_iff.
- destruct A2 as [A2|A2]; [left; apply Z.leb_gt | right; apply Z.ltb_ge]; lia.
- destruct A1 as [A1|A1]; [left; apply Z.leb_gt | right; apply Z.ltb_ge]; lia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
unfold in_vis, in_sh. split; apply existsb_false_forall; intros p Hp; [exact (proj1 (P p Hp)) | exact (proj2 (P p Hp))]. }
rewrite Hold. reflexivity. }
assert (Hgh : in_ghost E cs (bv_unsigned a) = false).
{ unfold in_ghost. apply existsb_false_forall. intros p Hp.
pose proof (proj1 (forallb_forall _ _) Hapg p Hp) as Hpp. cbv beta in Hpp.
destruct (split_lit (fst p)) as [pb pk] eqn:Hps.
apply andb_prop in Hpp as [Hpf Hap2].
destruct (flat_x_sound E _ (kn cs) pb pk (snd p) HK Hpf) as (Fp1 & Fp2 & Fp3).
pose proof (u_of_split E (fst p) pb pk Hps ltac:(lia)) as Up.
pose proof (ranges_apart_x_sound SEGS E _ (kn cs) _ _ _ _ _ _ HK Hap2) as A2.
fold S0 in A2. unfold elenZ in A2. pose proof Usn as U'. unfold elenZ in U'. rewrite ?U' in A2.
unfold uE. rewrite Up, Ua.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
apply andb_false_iff. destruct A2 as [A2|A2]; [left; apply Z.leb_gt | right; apply Z.ltb_ge]; lia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
unfold Mr, mrestrict. rewrite Hvis2.
apply (co_zero _ _ _ _ _ HC a Hhid1 Hm1 Hna Hlz Hgh). }
assert (Hfl : flat E (SA sb sk) (elenZ E (mkSrl (kn cs) n 3))).
{ unfold flat. fold S0. rewrite Usn. unfold CEIL in *.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
constructor; [|constructor; [|constructor]].
- cbn [kentry_ok]. split; [exact Hfl|]. intros d w Hd Hdw.
pose proof Hfl as (F1 & F2 & F3 & F4). fold S0 in F1, F2, F3, F4. fold S0.
assert (ES1 : S0 = estart E (SA sb sk)) by reflexivity.
destruct w as [|w']; [reflexivity|].
apply store_ok_of_all; [rewrite u64_lit by lia; lia|].
intros x Hx. rewrite u64_lit in Hx by lia.
unfold wview. replace x with (Z_to_bv 64 (S0 + (bv_unsigned x - S0))) by (apply bv_eq; rewrite u64_lit; pose proof (u64_range x); lia).
rewrite (BYTE (bv_unsigned x - S0)) by lia. discriminate.
- cbn [kentry_ok]. split; [exact Hfl|]. intros i Hi. fold S0. apply BYTE. exact Hi. }
destruct HC. constructor; cbn [cs2 a_ss a_maps a_totsz a_ylo a_eager a_vis a_abytes a_brk a_fd a_tidset a_hna a_hlz kn mk_ss s_regs s_log s_know];
try assumption; try reflexivity.
-
apply Forall_app. split; [exact HKsh | exact HKk].
- rewrite HA, A_bytes_app. lia.
- rewrite HA. apply MInv_app; [exact co_minv0|]. rewrite A_bytes_app, co_limit0. lia.
- intros a Ha. apply co_zero0. apply SUB. exact Ha.
Qed.
End SE.
Definition ext1 (E : env) (v : nat) (a : word) : env :=
Env (fun n => if Nat.eqb n v then a else ev E n) (eb E).
#[using="Type"] Lemma ext1_agree : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "?'Y='='_2yR0%211&Z9r2r3&X5r1%23341%63541pg@81po0<1pR<>1").
Proof.
intros E v a. split; [|reflexivity]. intros n Hn. cbn [ext1 ev].
destruct (Nat.eqb_spec n v); [lia | reflexivity].
Qed.
#[using="Type"] Lemma ext1_at : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "A'Y='='_2yR0%211'H&Y?&X5r3r2r1%43321%6213%83913pg@:1po0>1pR<@1").
Proof. intros. cbn [ext1 ev]. rewrite Nat.eqb_refl. reflexivity. Qed.
#[using="Type"] Lemma env_agree_le : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "C'='Y=&Z9r3r2r1%43321'Nr5r4%3221r6%:3139p031p081pR>>1pR<?1pgHA1pgFB1").
Proof. intros b b' E E' [H1 H2] Hle. split; [|exact H2]. intros n Hn. apply H1. lia. Qed.
#[using="Type"] Lemma env_agree_refl : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "8'='Y=&Z9r2r1%33211pR<51pgF71").
Proof. intros. split; [intros; reflexivity | reflexivity]. Qed.
#[using="Type"] Lemma env_agree_trans : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "A'='Y=&Z9r4r3r2%43321r5%63143r6%83136p031p061pRD<1pRB=1pR@>1pgF@1").
Proof. intros b E1 E2 E3 [A1 B1] [A2 B2]. split; [intros n Hn; rewrite A1 by lia; apply A2; lia | congruence]. Qed.
#[using="Type"] Lemma expr_vars_lt_eq : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "='='Y@'H'7&T3r2r1%3221&Z:%1243%83731pi@:1pgF<1").
Proof. intros b e. induction e; cbn; try rewrite IHe1, IHe2; try rewrite IHe; reflexivity. Qed.
#[using="Type"] Lemma kentry_vars_lt_eq : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "='='YE'H'7&U2r2r1%3221&Z;%1243%83731pS8:1pgF<1").
Proof.
intros b K. destruct K as [[? ?] | [? ?] | [? ?] | | | | [? ?] | [? ?] ? [? ?] ?| [? ?] ? ?| [? ?] ?];
cbn -[APK.expr_vars_lt AxSymRun3K.expr_vars_lt]; unfold APK.saddr_vars_lt, AxSymRun3K.saddr_vars_lt; cbn [a_base];
rewrite ?expr_vars_lt_eq; reflexivity.
Qed.
#[using="Type"] Lemma kn_vars_lt_eq : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "?'='<'YE%211'H'7&U=r2r1%3221&Z<%1243%83731pk0:1pgF>1").
Proof. intros b k. induction k; cbn [APK.kn_vars_lt AxSymRun3K.kn_vars_lt]; [reflexivity|]. rewrite kentry_vars_lt_eq, IHk. reflexivity. Qed.
#[using="Type"] Lemma sr_vars_lt_eq : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "?'='<'Y@%211'H'7&WBr2r1%3221&Z=%1243%83731pmL:1pgF>1").
Proof. intros b sr. induction sr; cbn [APK.sr_vars_lt AxSymRun3K.sr_vars_lt]; [reflexivity|]. rewrite expr_vars_lt_eq, IHsr. reflexivity. Qed.
#[using="Type"] Lemma edenot_agree' : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "L'='Y='Y@&Z9r4r3r2%43321'H'7&T3r5%2216(D%63521'_2yR0%211&Y<%128>%22@?%=3421p081p0@1pi@F1pR>H1pR<I1pgFK1").
Proof. intros. eapply edenot_agree; [eassumption | rewrite <- expr_vars_lt_eq; assumption]. Qed.
#[using="Type"] Lemma know_ok_agree' : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "Q6'='Y='_2yR0%211'@y8%511%311p051'<'YE%211&Z9r5r4r3%43321'H'7&U=r6r2%3221(D%73621&Z6vZJ%2417=<%3428?>p021p061p0?1pk0E1pTDI1pR>Q21pR<Q31pgFQ51").
Proof. intros. eapply know_ok_agree; [eassumption | rewrite <- kn_vars_lt_eq; eassumption | assumption]. Qed.
#[using="Type"] Lemma regs_ok_agree' : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "Q2'='Y='<'Y@%211&R8y5'_2yR0%211%5241&Z9r5r4r3%43321'H'7&WBr6%2216(D%63521&Z7%135;:%236=<p021p051p0=1pTNC1pmLJ1pR>N1pR<O1pgFQ11").
Proof. intros. eapply regs_ok_agree; [eassumption | rewrite <- sr_vars_lt_eq; eassumption | assumption]. Qed.
#[using="HOLES_agree"] Lemma sd_agree : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "N&ZC'Y=&QF'W<&Z9v^<r4r3%43321'H'7&W>r2%2281(D%63521&XHr7r6%3421=<r5%5441?>%=3F31p081p0@1pm@F1piNH1pR>J1pR<K1pR:M1").
Proof.
intros D E E' fs s Hag. induction s; cbn [shape_vars_lt sd]; intros H; try reflexivity.
- rewrite IHs by exact H. unfold Wp. replace (flat_map (piece_den E') ps) with (flat_map (piece_den E) ps); [reflexivity|].
apply flat_map_ext. intros [bs|k]; cbn [piece_den]; [reflexivity|]. destruct Hag as [_ Heb]. rewrite Heb. reflexivity.
- apply andb_prop in H as [H1 H2]. rewrite IHs1, IHs2 by assumption. reflexivity.
- apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
rewrite IHs1, IHs2 by assumption. rewrite (edenot_agree' nx0 E E' e Hag H1). reflexivity.
- apply HOLES_agree. exact Hag.
Qed.
#[using="Type"] Lemma t_exit_has_nil : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "='_2yR0%211&QF&ZFr2r1(?'QM%211%63541piN81phL:1").
Proof. intros. unfold t_exit. apply t_emit_has_nil. Qed.
#[using="HOLES_nil"] Lemma sd_has_nil : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "F'<'QM%211!po>21'Y=&QF'W<r4(?%119%311&XHr5r3r2%4538216p061pm@;1piN=1pR<?1pR:A1").
Proof.
intros D E fs s HD. induction s; cbn [sd].
- reflexivity.
- apply t_exit_has_nil.
- apply t_emit_has_nil.
- left. exact IHs1.
- destruct (_ <=? _)%Z; assumption.
- apply HOLES_nil.
- exact HD.
Qed.
#[using="Type"] Lemma t_alt2_nil_l : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK ">&ZCr1(?'QM%211%411&ZE&ZD&ZGr2%3221%5212p071pfH=1").
Proof. intros T HT tr. unfold t_alt2, t_nil. split; [intros [->|H]; assumption | intros H; right; exact H]. Qed.
#[using="Type"] Lemma t_alt2_nil_r : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK ">&ZCr1(?'QM%211%411&ZE&ZDr2&ZG%3221%5213p071pfH=1").
Proof. intros T HT tr. unfold t_alt2, t_nil. split; [intros [H| ->]; assumption | intros H; left; exact H]. Qed.
#[using="Type"] Lemma t_eq_alt2 : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "C&ZC&ZEr4r3%3221r2%5231&ZDr6%2217r5%4218%;231p071p0:1pg2?1pg0@1pfNA1pfLB1").
Proof. intros TA TA' TB TB' HA HB tr. unfold t_alt2. split; (intros [H|H]; [left; apply HA | right; apply HB]; exact H). Qed.
#[using="nx0 HS XN XE XB"] Lemma t_eq_refl' : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "5&ZC&ZEr1%2211pfH41").
Proof. intros T tr. tauto. Qed.
#[using="nx0 HS XN XE XB HOLES_nil"] Lemma sd_salt2 : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "Q0'<'QM%211!po>21'Y=&QF'W<r5(?%119%311&ZE&ZD&XHr6r4r3%443:21r2%645<41%8231&W6%1264%:49@81%=241p0?1pgFD1pg@E1piNG1pR<I1pR:K1").
Proof.
intros D E fs a b HD.
assert (Ha : sd D E fs a []) by (apply sd_has_nil; exact HD).
assert (Hb : sd D E fs b []) by (apply sd_has_nil; exact HD).
unfold salt2. destruct a; destruct b; cbn [sd] in *;
first [ apply t_alt2_nil_l; assumption | apply t_alt2_nil_r; assumption | apply t_eq_refl' ].
Qed.
#[using="Type"] Lemma t_alt2_idem' : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "<&ZC&ZEr2r1%3221&ZDr3%2215%7212p051pfJ:1pfH;1").
Proof. intros T T' H tr. unfold t_alt2. split; [intros [X|X]; [exact X | apply H; exact X] | intros X; left; exact X]. Qed.
#[using="nx0 HS XN XE XB HOLES_flat"] Lemma hole_only_den : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "K&ZC'Y=&QF'W<'H'7&T>r1%211(D%63521&ZE&XHr5r4r3r2%544321vQ?(2%23165%:241p0<1pm@D1piNF1pR<H1pR:J1").
Proof.
intros D E fs s. induction s as [| c | fd ps s IH | a IHa b IHb | e mid a IHa b IHb | h |]; intros H; cbn [hole_only] in H; try discriminate.
- apply andb_prop in H as [Ha Hb]. cbn [sd]. eapply t_eq_trans; [apply t_eq_alt2; [apply IHa; exact Ha | apply IHb; exact Hb] |].
apply t_alt2_idem'. apply t_eq_refl'.
- apply andb_prop in H as [Ha Hb]. cbn [sd]. destruct (_ <=? _)%Z; [apply IHa; exact Ha | apply IHb; exact Hb].
- cbn [sd]. rewrite (HOLES_flat h 0%nat E E fs). apply t_eq_refl'.
Qed.
#[using="nx0 HS XN XE XB HOLES_flat"] Lemma hole_only_eq : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "L&ZC'Y=&QF'W<'H'7&T>r2%211(D%63521&ZE&XHr7r6r5r4%544321r3%746541%9231p0;1p0<1pgFD1pg@E1piNG1pR<I1pR:K1").
Proof.
intros D E fs a b Ha Hb. eapply t_eq_trans; [apply hole_only_den; exact Ha | apply t_eq_sym; apply hole_only_den; exact Hb].
Qed.
#[using="Type"] Lemma salt2_vars : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "G'='W<'H'7&W>r3r2%3221(D%73621r4%7215%:3914r5&W6%125:%<231%?3>19p061p0:1po@C1po>D1pgFF1").
Proof.
intros b x y Hx Hy. unfold salt2.
destruct x; destruct y; cbn [shape_vars_lt] in *; rewrite ?Hx, ?Hy; try reflexivity; try assumption.
Qed.
Definition node1_stmt (pre : acs -> bool) (node : acs -> option acs) : Prop :=
forall cs cs' E R FULL model T,
cs_ok E cs R FULL model -> pre cs = true -> node cs = Some cs' ->
(forall E' R' FULL' model',
env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> cs_ok E' cs' R' FULL' model' -> m_fs model' = m_fs model ->
srealizes SEGS scfg (cfg R' (pc cs') FULL' model') T) ->
srealizes SEGS scfg (cfg R (pc cs) FULL model) T.
Definition always (cs : acs) : bool := true.
Definition sys_stmt (y : snode) : Prop := node1_stmt (is_ecall_at SEGS) (node_sys A nx0 y).
Definition x_stmt (x : xnode) : Prop := forall args, node1_stmt always (node_x SEGS A nx0 x args).
Definition fresh_stmt : Prop := forall r logc base, node1_stmt always (fun cs => node_fresh nx0 cs r logc base).
Definition join_stmt : Prop := forall b off n, node1_stmt always (fun cs => node_join SEGS cs b off n).
Definition brk2_stmt : Prop :=
forall cs csa csb E R FULL model TA TB,
cs_ok E cs R FULL model -> is_ecall_at SEGS cs = true -> node_brk2 A LIMIT cs = Some (csa, csb) ->
(forall E' R' FULL' model',
env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> cs_ok E' csa R' FULL' model' -> m_fs model' = m_fs model ->
srealizes SEGS scfg (cfg R' (pc csa) FULL' model') TA) ->
(forall E' R' FULL' model',
env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> cs_ok E' csb R' FULL' model' -> m_fs model' = m_fs model ->
srealizes SEGS scfg (cfg R' (pc csb) FULL' model') TB) ->
t_eq TA TB ->
srealizes SEGS scfg (cfg R (pc cs) FULL model) (t_alt2 TA TB).
Definition exit_stmt : Prop :=
forall cs code E R FULL model,
cs_ok E cs R FULL model -> is_ecall_at SEGS cs = true -> node_exit cs = Some code ->
srealizes SEGS scfg (cfg R (pc cs) FULL model) (t_exit (Z_to_bv 64 code) (m_fs model)).
Definition ext_stmt : Prop := forall id args, node1_stmt always (XN id args).
Definition ext2_stmt : Prop :=
forall id args cs csa csb E R FULL model TA TB,
cs_ok E cs R FULL model -> XB id args cs = Some (csa, csb) ->
(forall E' R' FULL' model',
env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> cs_ok E' csa R' FULL' model' -> m_fs model' = m_fs model ->
srealizes SEGS scfg (cfg R' (pc csa) FULL' model') TA) ->
(forall E' R' FULL' model',
env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> cs_ok E' csb R' FULL' model' -> m_fs model' = m_fs model ->
srealizes SEGS scfg (cfg R' (pc csb) FULL' model') TB) ->
srealizes SEGS scfg (cfg R (pc cs) FULL model) (t_alt2 TA TB).
Definition mm2_stmt (node : acs -> option (acs * acs)) : Prop :=
forall cs csa csb E R FULL model TB,
cs_ok E cs R FULL model -> is_ecall_at SEGS cs = true -> node cs = Some (csa, csb) ->
(forall E' R' FULL' model',
env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> cs_ok E' csa R' FULL' model' -> m_fs model' = m_fs model ->
srealizes SEGS scfg (cfg R' (pc csa) FULL' model') TB) ->
(forall E' R' FULL' model',
env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> cs_ok E' csb R' FULL' model' -> m_fs model' = m_fs model ->
srealizes SEGS scfg (cfg R' (pc csb) FULL' model') TB) ->
srealizes SEGS scfg (cfg R (pc cs) FULL model) TB.
Definition mm3_stmt (node : acs -> option (acs * acs * list acs)) : Prop :=
forall cs csa csb cscs E R FULL model TB,
cs_ok E cs R FULL model -> is_ecall_at SEGS cs = true -> node cs = Some (csa, csb, cscs) ->
(forall E' R' FULL' model',
env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> cs_ok E' csb R' FULL' model' -> m_fs model' = m_fs model ->
srealizes SEGS scfg (cfg R' (pc csb) FULL' model') TB) ->
srealizes SEGS scfg (cfg R (pc cs) FULL model) TB.
Definition emit_stmt : Prop :=
forall id args cs fd ps cs' E R FULL model T,
cs_ok E cs R FULL model -> XE id args cs = Some (fd, ps, cs') -> T [] ->
(forall E' R' FULL' model',
env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> cs_ok E' cs' R' FULL' model' -> m_fs model' = m_fs model ->
srealizes SEGS scfg (cfg R' (pc cs') FULL' model') T) ->
srealizes SEGS scfg (cfg R (pc cs) FULL model) (t_emit (Wp E fd ps) T).
Definition holes_stmt : Prop :=
forall h ch, HS h = Some ch ->
forall E R FULL model, cs_ok E ch R FULL model ->
srealizes SEGS scfg (cfg R (pc ch) FULL model) (HOLES h E (m_fs model)).
Hypothesis node_sys_sound : forall y, sys_stmt y.
Hypothesis node_brk2_sound : brk2_stmt.
Hypothesis node_mmap2_sound : forall split : bool, mm2_stmt (node_mmap2 A nx0 LIMIT split).
Hypothesis node_mmapin_sound : forall hole : bool, mm3_stmt (node_mmapin A LIMIT hole).
Hypothesis node_mprotect2_sound : mm2_stmt (node_mprotect2 A LIMIT).
Hypothesis node_exit_sound : exit_stmt.
Hypothesis node_x_sound : forall x, x_stmt x.
Hypothesis node_join_sound : join_stmt.
Hypothesis node_ext_sound : ext_stmt.
Hypothesis node_emit_sound : emit_stmt.
Hypothesis node_ext2_sound : ext2_stmt.
Hypothesis HS_sound : holes_stmt.
#[using="Type"] Lemma split_sound : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "RB'S6'Y@'Q3'Y=&R8y5'_2yR0%211%5241'@y8%611%311p061'QL'X4r4r9r3r2r1%6554321'H'B%12GG%@11&Y>&U7r:%211%421=(4(Ar7r6%34Q2Q221%52<1%?3<71'G&[3&_3&Y<%128>%32Q51%521K&W8r<(8'YE(Y5r;%231Q2G%I16%63521%9281r5%Q95G2F1Q8p0=1&[4%12Q:@&[1+1%22Q21r8%?3>21%B3A1=%E2D1%QD5Q21Q1<QCp091%O2<1p0Q11p0QB1pl4QJ1pRFQL1pTNR21pR<R91pj<R;1pkHR<1pl0R=1pi@R?1phNRA1").
Proof.
intros cs e mid lo hi E R FULL model HC Hr.
pose proof (erange_sound SEGS E _ (kn cs) e lo hi (co_know _ _ _ _ _ HC) Hr) as Hb.
split; intros Hm; apply cs_ok_set_kn; [exact HC| |exact HC|];
(constructor; [cbn [kentry_ok]; lia | exact (co_know _ _ _ _ _ HC)]).
Qed.
Section SE.
Local Abbreviation SEC_T_kn_contra_sound := (ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "N'Y='_2yR0%211'@y8%511%311p051'<'YE%211&Z6vZJr3r2r1%544321'H'7&U9%116(D%53421'Ep021p091pk0@1pTDD1pR<M1")) (only parsing).
Variable E : ltac:(sec_ty2 constr:(SEC_T_kn_contra_sound) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_kn_contra_sound) 1%nat 0%nat).
Variable k : ltac:(sec_ty2 constr:(SEC_T_kn_contra_sound) 2%nat 0%nat).
Lemma kn_contra_sound : ltac:(sec_stmt2 constr:(SEC_T_kn_contra_sound) 3%nat 0%nat).
Proof using Type E M k.
intros HK H.
unfold kn_contra in H. apply existsb_exists in H as (K & Hin & HKb).
pose proof (proj1 (Forall_forall _ _) HK K Hin) as HKK.
destruct K as [| | | | |e lo hi| | | |]; try discriminate. cbn [kentry_ok] in HKK.
destruct (Z.ltb hi lo) eqn:Hlt; [apply Z.ltb_lt in Hlt; lia|].
assert (GEN : forall c ts, lin_of e = (c, ts) ->
match lin_range (erange k) c ts with
| Some (a, b) => (Z.leb 0 a && Z.ltb b two64 && (Z.ltb b lo || Z.ltb hi a))%bool
| None => false end = true -> False).
{ intros c ts Hle Hm.
destruct (lin_range (erange k) c ts) as [[a b]|] eqn:Hlr; [|discriminate].
apply andb_prop in Hm as [Hm Hd]. apply andb_prop in Hm as [Ha Hb].
apply Z.leb_le in Ha. apply Z.ltb_lt in Hb. unfold two64 in Hb.
pose proof (lin_range_sound E (erange k) (fun a lo hi Ha => erange_sound SEGS E M k a lo hi HK Ha) _ _ _ _ Hlr) as Hbd.
pose proof (lin_of_sound E e) as [q Hq]. unfold lden, AX2SK.uE in Hq. rewrite Hle in Hq. cbn [fst snd] in Hq.
pose proof (u64_range (edenot E e)).
assert (q = 0)%Z by nia. subst q.
apply orb_prop in Hd as [Hd|Hd]; apply Z.ltb_lt in Hd; lia. }
destruct e; try discriminate;
(destruct (lin_of _) as [c [|t1 [|t2 ts]]] eqn:Hle; try discriminate; exact (GEN _ _ eq_refl HKb)).
Qed.
End SE.
#[using="Type"] Lemma estart_SA : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "F'Y='Y@'Q3'H&Z4r3(Y8r2r1%3221%6251&[1&_3yR0&Y<%12:8%4231%6219%?3@81pk0A1pgFC1pR<E1").
Proof. reflexivity. Qed.
Section SE.
Local Abbreviation SEC_T_xlo1_sound := (ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "Q:'Y='_2yR0%211'@y8%511%311p051'<'YE%211'Y@'Q3&Z6vZJr5r4r3%544321'H%A18&WJ%1265(4r2%22=1%73641&[3&_3&Y<r7%221?%42O1%62@1p081p0A1pkHH1pi@J1pk0L1pTDQ01pR<Q91")) (only parsing).
Variable E : ltac:(sec_ty2 constr:(SEC_T_xlo1_sound) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_xlo1_sound) 1%nat 0%nat).
Variable k : ltac:(sec_ty2 constr:(SEC_T_xlo1_sound) 2%nat 0%nat).
Lemma xlo1_sound : ltac:(sec_stmt2 constr:(SEC_T_xlo1_sound) 3%nat 0%nat).
Proof using Type E M k.
intros e lo HK H.
unfold xlo1 in H.
assert (LIT : forall z, e = ELit z -> Some (zlit64 z) = Some lo -> lo <= bv_unsigned (edenot E e)).
{ intros z -> Hs. injection Hs as <-. cbn [edenot]. rewrite zlit64_eq, u_lit64. lia. }
destruct e; [exact (LIT _ eq_refl H)|..]; clear LIT;
(destruct (erange k _) as [[l1 h1]|] eqn:He; [pose proof (erange_sound SEGS E M k _ l1 h1 HK He)|];
destruct (lin_brange k _) as [[l2 h2]|] eqn:Hb; [pose proof (lin_brange_sound SEGS E M k _ l2 h2 HK Hb)| |pose proof (lin_brange_sound SEGS E M k _ l2 h2 HK Hb)|];
[..| destruct (lin_srange k _) as [[l3 h3]|] eqn:Hs; [pose proof (lin_srange_sound SEGS E M k _ l3 h3 HK Hs)|]];
try discriminate; injection H as <-; lia).
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_xhi1_sound := (ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "Q:'Y='_2yR0%211'@y8%511%311p051'<'YE%211'Y@'Q3&Z6vZJr5r4r3%544321'H%A18&WH%1265(4r2%22=1%73641&[3&_3&Y<r7%221?%42O1%621@p081p0A1pj<H1pi@J1pk0L1pTDQ01pR<Q91")) (only parsing).
Variable E : ltac:(sec_ty2 constr:(SEC_T_xhi1_sound) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_xhi1_sound) 1%nat 0%nat).
Variable k : ltac:(sec_ty2 constr:(SEC_T_xhi1_sound) 2%nat 0%nat).
Lemma xhi1_sound : ltac:(sec_stmt2 constr:(SEC_T_xhi1_sound) 3%nat 0%nat).
Proof using Type E M k.
intros e hi HK H.
unfold xhi1 in H.
assert (LIT : forall z, e = ELit z -> Some (zlit64 z) = Some hi -> bv_unsigned (edenot E e) <= hi).
{ intros z -> Hs. injection Hs as <-. cbn [edenot]. rewrite zlit64_eq, u_lit64. lia. }
destruct e; [exact (LIT _ eq_refl H)|..]; clear LIT;
(destruct (erange k _) as [[l1 h1]|] eqn:He; [pose proof (erange_sound SEGS E M k _ l1 h1 HK He)|];
destruct (lin_brange k _) as [[l2 h2]|] eqn:Hb; [pose proof (lin_brange_sound SEGS E M k _ l2 h2 HK Hb)| |pose proof (lin_brange_sound SEGS E M k _ l2 h2 HK Hb)|];
[..| destruct (lin_srange k _) as [[l3 h3]|] eqn:Hs; [pose proof (lin_srange_sound SEGS E M k _ l3 h3 HK Hs)|]];
try discriminate; injection H as <-; lia).
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_deand_sound := (ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "QB'Y='Y@'Q3'H'B%1243&SHr3%211(Ar2r1%34;:21%:3851'G&[3z%2217'I%4238%529=%7221&_3yR0&Y<r6r5%3221%6251&[5&[:r4%8271%;2:1%421G&[9+2+R0%3221%:251%Q53Q6<1%K2D1qm<Q81%I2Q91%N2K1p0Q01pm@Q<1piBQ>1pi@Q?1pR<QA1")) (only parsing).
Variable E : ltac:(sec_ty2 constr:(SEC_T_deand_sound) 0%nat 0%nat).
Lemma deand_sound : ltac:(sec_stmt2 constr:(SEC_T_deand_sound) 1%nat 0%nat).
Proof using Type E.
intros e.
induction e as [z|n|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|u w sx a IHa|bk bo bn bw];
intros e' s Hd;
try (cbn [deand] in Hd; injection Hd as <- <-; split; [lia|]; exists 0; split; [lia|];
rewrite Z.sub_0_r, Z.mod_small by (apply u64_range); reflexivity).
cbn [deand] in Hd. fold (deand a) (deand b) in Hd.
destruct op;
try (injection Hd as <- <-; split; [lia|]; exists 0; split; [lia|];
rewrite Z.sub_0_r, Z.mod_small by (apply u64_range); reflexivity).
-
destruct (deand a) as [a' s1] eqn:Ha. destruct (deand b) as [b' s2] eqn:Hb. injection Hd as <- <-.
destruct (IHa a' s1 eq_refl) as [Hs1 [ra [Hra Ea]]]. destruct (IHb b' s2 eq_refl) as [Hs2 [rb [Hrb Eb]]].
split; [lia|]. exists (ra + rb). split; [lia|].
cbn [edenot]. rewrite !u_add64, Ea, Eb. unfold two64.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
pose proof (u64_range (edenot E a')). pose proof (u64_range (edenot E b')).
set (A1 := bv_unsigned (edenot E a')) in *. set (B1 := bv_unsigned (edenot E b')) in *.
nia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
-
destruct b as [m| | | | | | |];
try (injection Hd as <- <-; split; [lia|]; exists 0; split; [lia|];
rewrite Z.sub_0_r, Z.mod_small by (apply u64_range); reflexivity).
cbv zeta in Hd.
set (m' := m mod two64) in Hd. set (j := Z.log2 (two64 - m')) in Hd.
destruct (Z.eqb (two64 - m') (2 ^ j) && Z.leb j 48)%bool eqn:Ht;
[|injection Hd as <- <-; split; [lia|]; exists 0; split; [lia|];
rewrite Z.sub_0_r, Z.mod_small by (apply u64_range); reflexivity].
apply andb_prop in Ht as [Hm Hj]. apply Z.eqb_eq in Hm. apply Z.leb_le in Hj.
assert (Hj0 : 0 <= j) by (unfold j; apply Z.log2_nonneg).
destruct (deand a) as [a' s0] eqn:Ha. injection Hd as <- <-.
destruct (IHa a' s0 eq_refl) as [Hs0 [ra [Hra Ea]]].
assert (Hp : 0 < 2 ^ j) by (apply Z.pow_pos_nonneg; lia).
split; [lia|].
set (X := bv_unsigned (edenot E a)) in *.
pose proof (u64_range (edenot E a)) as HX. fold X in HX.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
assert (Hr : 0 <= X mod 2 ^ j < 2 ^ j) by (apply Z.mod_pos_bound; lia).
assert (Hr2 : X mod 2 ^ j <= X) by (apply Z.mod_le; lia).
exists (ra + X mod 2 ^ j). split; [lia|].
cbn [edenot]. rewrite u_and64, u_lit64. fold X. fold m'.
assert (Hm' : 0 <= m' < two64) by (unfold m'; apply Z.mod_pos_bound; unfold two64; lia).
replace m' with (2 ^ 64 - 2 ^ j) by (unfold two64 in *; lia).
rewrite land_highmask by lia.
pose proof (u64_range (edenot E a')) as HA'. set (A' := bv_unsigned (edenot E a')) in *.
set (r := X mod 2 ^ j) in *. clearbody r.
rewrite Ea. rewrite Ea in HX. nia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_deand_vars := (ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "N'='Y@'Q3'H'B%1243&SHr3%211(Ar2r1%34;:21%:3851'7&T3r5r4%3221(D%A3621r6%7215%D3914p041p0<1pm@H1piBJ1pi@K1ph0M1")) (only parsing).
Variable bnd : ltac:(sec_ty2 constr:(SEC_T_deand_vars) 0%nat 0%nat).
Lemma deand_vars : ltac:(sec_stmt2 constr:(SEC_T_deand_vars) 1%nat 0%nat).
Proof using Type bnd.
intros e.
induction e as [z|n|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|u w sx a IHa|bk bo bn bw];
intros e' s Hd Hv; try (cbn [deand] in Hd; injection Hd as <- <-; exact Hv).
cbn [deand] in Hd. fold (deand a) (deand b) in Hd.
pose proof Hv as Hv0.
cbn [APK.expr_vars_lt] in Hv. apply andb_prop in Hv as [Hva Hvb].
destruct op; try (injection Hd as <- <-; exact Hv0).
- destruct (deand a) as [a' s1] eqn:Ha. destruct (deand b) as [b' s2] eqn:Hb. injection Hd as <- <-.
cbn [APK.expr_vars_lt]. rewrite (IHa a' s1 eq_refl Hva), (IHb b' s2 eq_refl Hvb). reflexivity.
- destruct b as [m| | | | | | |]; try (injection Hd as <- <-; exact Hv0).
cbv zeta in Hd.
destruct (Z.eqb _ _ && Z.leb _ 48)%bool; [|injection Hd as <- <-; exact Hv0].
destruct (deand a) as [a' s0] eqn:Ha. injection Hd as <- <-. exact (IHa a' s0 eq_refl Hva).
Qed.
End SE.
#[using="Type"] Lemma xb2_sound : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "QC'Y='_2yR0%211'@y8%511%311p051'<'YE%211'Y@'Q3&Z6vZJr6r5r4%544321'H'B%1299%C11&WG%1287(4(Ar3r2%34AA21%5291%<3971'G&[3&_3&Y<r8%221E%42Q51%62F1%722=%9221p0;1p0I1pj<Q01pkHQ11pi@Q31pk0Q51pTDQ91pR<QB1").
Proof.
intros E M k e lo hi HK H. unfold xb2 in H.
set (plain := match xlo1 k e, xhi1 k e with Some lo, Some hi => Some (lo, hi) | _, _ => None end) in H.
assert (HP : forall lo hi, plain = Some (lo, hi) -> lo <= bv_unsigned (edenot E e) <= hi).
{ intros l h Hp. unfold plain in Hp.
destruct (xlo1 k e) as [l1|] eqn:H1; [|discriminate]. destruct (xhi1 k e) as [h1|] eqn:H2; [|discriminate].
injection Hp as <- <-. split; [eapply xlo1_sound; eassumption | eapply xhi1_sound; eassumption]. }
destruct (deand e) as [e' s] eqn:Hd.
destruct (deand_sound E e e' s Hd) as [Hs [rho [Hrho Ee]]].
destruct (Z.eqb s 0); [exact (HP lo hi H)|].
destruct (xlo1 k e') as [lo'|] eqn:H1; [|exact (HP lo hi H)].
destruct (xhi1 k e') as [hi'|] eqn:H2; [|exact (HP lo hi H)].
destruct (Z.leb s lo') eqn:Hsl; [|exact (HP lo hi H)]. apply Z.leb_le in Hsl.
pose proof (xlo1_sound E M k e' lo' HK H1) as L1. pose proof (xhi1_sound E M k e' hi' HK H2) as L2.
pose proof (u64_range (edenot E e')) as R'.
assert (Hue : bv_unsigned (edenot E e) = bv_unsigned (edenot E e') - rho) by (rewrite Ee; apply Z.mod_small; lia).
destruct plain as [[l0 h0]|].
- specialize (HP l0 h0 eq_refl). injection H as <- <-. lia.
- injection H as <- <-. lia.
Qed.
#[using="Type"] Lemma xlo2_sound : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "Q:'Y='_2yR0%211'@y8%511%311p051'<'YE%211'Y@'Q3&Z6vZJr5r4r3%544321'H%A18&WK%1265(4r2%22=1%73641&[3&_3&Y<r7%221?%42O1%62@1p081p0A1pkHH1pi@J1pk0L1pTDQ01pR<Q91").
Proof.
intros E M k e lo HK H. unfold xlo2 in H. destruct (xb2 k e) as [[l h]|] eqn:Hb; [|discriminate].
injection H as <-. exact (proj1 (xb2_sound E M k e l h HK Hb)).
Qed.
#[using="Type"] Lemma xhi2_sound : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "Q:'Y='_2yR0%211'@y8%511%311p051'<'YE%211'Y@'Q3&Z6vZJr5r4r3%544321'H%A18&WI%1265(4r2%22=1%73641&[3&_3&Y<r7%221?%42O1%621@p081p0A1pj<H1pi@J1pk0L1pTDQ01pR<Q91").
Proof.
intros E M k e hi HK H. unfold xhi2 in H. destruct (xb2 k e) as [[l h]|] eqn:Hb; [|discriminate].
injection H as <-. exact (proj2 (xb2_sound E M k e l h HK Hb)).
Qed.
#[using="Type"] Lemma residue_fact_sound : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "QK'Y='_2yR0%211'@y8%511%311p051'<'YE%211'Y@&Z6vZJr7r5r3%544321'H&Y<r2%2271r8%4217%63F31'Q3'B%12@2&SHr6%211(Ar1%24F8=1%@3741r;%A21Dr<%C21F%E3Q531p061pm@@1piBO1r9&W2r4%23AO1%Q34Q24Q11p061p0I1p0Q11plBQ81pi@Q91pk0Q;1pTFQ?1pTDQ@1pR>QI1pR<QJ1").
Proof.
intros E E' M M' k e ne HK Hne Hag. unfold residue_fact.
destruct (deand e) as [e' s] eqn:Hd. destruct (Z.ltb 0 s) eqn:Hs; [|constructor].
destruct (xlo1 k e') as [lo'|] eqn:H1; [|constructor]. destruct (xhi1 k e') as [hi'|] eqn:H2; [|constructor].
destruct (Z.leb s lo') eqn:Hsl; [|constructor]. apply Z.leb_le in Hsl.
constructor; [|constructor]. cbn [kentry_ok]. unfold esub. rewrite mkAlu_denot, u_sub64, Hne, (Hag e' s eq_refl).
destruct (deand_sound E e e' s Hd) as [Hs0 [rho [Hrho Ee]]].
pose proof (xlo1_sound E M k e' lo' HK H1) as L1. pose proof (u64_range (edenot E e')) as R'.
assert (Hue : bv_unsigned (edenot E e) = bv_unsigned (edenot E e') - rho) by (rewrite Ee; apply Z.mod_small; lia).
rewrite Hue. replace (bv_unsigned (edenot E e') - (bv_unsigned (edenot E e') - rho)) with rho by lia.
rewrite Z.mod_small by lia. lia.
Qed.
#[using="Type"] Lemma fact_ok_sound : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "Q2'Y='_2yR0%211'@y8%511%311p051'<'YE%211&Z6vZJr4r3r2%544321'H'7&T4%1265(D%53421&Z5r6r5%34>21<p051p0<1pS8D1pk0D1pTDH1pR<Q11").
Proof.
intros E M k K HK H. destruct K as [| | | |e m|e lo hi| |[b1 k1] n1 [b2 k2] n2| |]; try discriminate; cbn [fact_ok] in H.
- apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
apply Z.ltb_lt in H1. apply Z.eqb_eq in H2. apply Z.leb_le in H3. cbn [kentry_ok]. split; [exact H1|].
destruct (ealign_sound SEGS E M k e HK) as [Hr Hd].
rewrite H2. apply Z.mod_divide; [lia|]. eapply Z.divide_trans; [|exact Hd]. apply pow2_divide_le. split; [apply Z.log2_nonneg | exact H3].
- destruct (xlo2 k e) as [l|] eqn:Hl; [|discriminate]. destruct (xhi2 k e) as [h|] eqn:Hh; [|discriminate].
apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
pose proof (xlo2_sound E M k e l HK Hl). pose proof (xhi2_sound E M k e h HK Hh). cbn [kentry_ok]. lia.
- cbn [kentry_ok]. exact (ranges_apart_x_sound SEGS E M k b1 k1 n1 b2 k2 n2 HK H).
Qed.
#[using="Type"] Lemma fact_sound : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "Q?'Y='S6&R8y5'_2yR0%211%5241'@y8%611%311p061'QL'YE'X4r6r5r4r3r2%6554321'H'7&T4&U7%11:%3217(D%73621r8&S7r7(8(?%11E%33FA1%6251%G581FEDp0:1p0C1pS8K1pl4M1pRFO1pTNQ51phNQ<1pR<Q>1").
Proof.
intros E cs R FULL model K HC H. unfold add_kn. apply cs_ok_set_kn; [exact HC|].
constructor; [eapply fact_ok_sound; [exact (co_know _ _ _ _ _ HC) | exact H] | exact (co_know _ _ _ _ _ HC)].
Qed.
#[using="Type"] Lemma regs_ok_ext_eq : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "J'Y='<'Y@%211&R8y5'_2yR0%211%5241'Hr3r2%33:21&Z7r5r4%33215r6%53138p031p081pTN=1pmND1pmLE1pR<I1").
Proof. intros; subst; assumption. Qed.
Section SE.
Local Abbreviation SEC_T_entails_sound := (ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "Q>'Y='S6&R8y5'_2yR0%211%5241'@y8%611%311p061'QL'X4r6r5r3r2r1%6554321'H'7&SN%1298(D%53421'Gr8r4%@52?>1='Q3&VL%11Br7%311%?3531%:271p0<1p0C1pl4K1pRFM1pTNQ31phHQ:1phNQ;1pR<Q=1")) (only parsing).
Variable E : ltac:(sec_ty2 constr:(SEC_T_entails_sound) 0%nat 0%nat).
Variable cs : ltac:(sec_ty2 constr:(SEC_T_entails_sound) 1%nat 0%nat).
Variable ch : ltac:(sec_ty2 constr:(SEC_T_entails_sound) 2%nat 0%nat).
Variable R : ltac:(sec_ty2 constr:(SEC_T_entails_sound) 3%nat 0%nat).
Variable FULL : ltac:(sec_ty2 constr:(SEC_T_entails_sound) 4%nat 0%nat).
Variable model : ltac:(sec_ty2 constr:(SEC_T_entails_sound) 5%nat 0%nat).
Lemma entails_sound : ltac:(sec_stmt2 constr:(SEC_T_entails_sound) 6%nat 0%nat).
Proof using Type E cs ch R FULL model.
intros HC H.
unfold entails in H.
repeat match type of H with (_ && _)%bool = true => apply andb_prop in H as [H ?X] end.
rename H into Hpc. apply Z.eqb_eq in Hpc. split; [|symmetry; exact Hpc].
match goal with Hl : match s_log (a_ss ch) with _ => _ end = true |- _ => rename Hl into HL; destruct (s_log (a_ss ch)) eqn:HL'; [clear HL; rename HL' into HL|discriminate] end.
match goal with Hr : list_eqb expr_eqb _ _ = true |- _ => apply (list_eqb_eq expr_eqb expr_eqb_eq) in Hr; rename Hr into Hregs end.
match goal with Hm : list_eqb amap_eqb _ _ = true |- _ => apply (list_eqb_eq amap_eqb amap_eqb_eq) in Hm; rename Hm into Hmaps end.
match goal with Ha : list_eqb pair_eqb (a_vis cs) _ = true |- _ => apply (list_eqb_eq pair_eqb pair_eqb_eq) in Ha; rename Ha into Hallow end.
match goal with Hg : list_eqb pair_eqb (a_ghost cs) _ = true |- _ => apply (list_eqb_eq pair_eqb pair_eqb_eq) in Hg; rename Hg into Hghost end.
match goal with Hb : expr_eqb (a_brk cs) _ = true |- _ => apply expr_eqb_eq in Hb; rename Hb into Hbrk end.
match goal with Hf : afd_eqb _ _ = true |- _ => apply afd_eqb_eq in Hf; rename Hf into Hfd end.
match goal with Ht : Bool.eqb _ _ = true |- _ => apply eqb_prop in Ht; rename Ht into Htid end.
match goal with Hh : list_eqb hop_eqb (a_hna cs) _ = true |- _ => apply (list_eqb_eq hop_eqb hop_eqb_eq) in Hh; rename Hh into Hhna end.
match goal with Hh : list_eqb hop_eqb (a_hlz cs) _ = true |- _ => apply (list_eqb_eq hop_eqb hop_eqb_eq) in Hh; rename Hh into Hhlz end.
match goal with Hk : forallb _ (kn ch) = true |- _ => rename Hk into Hkn end.
repeat match goal with Hz : Z.leb _ _ = true |- _ => apply Z.leb_le in Hz end.
assert (HA : allowA E ch = allowA E cs) by (unfold allowA; rewrite Hallow, Hghost; reflexivity).
assert (HH : hid E ch model = hid E cs model) by (apply hid_ext; symmetry; exact Hallow).
destruct HC; constructor; rewrite <- ?Hregs, <- ?Hmaps, <- ?Hallow, <- ?Hghost, <- ?Hbrk, <- ?Hfd, <- ?Htid, <- ?Hhna, <- ?Hhlz, ?HA; try assumption.
- unfold Mr. rewrite HH. unfold know_ok. apply Forall_forall. intros K Hin.
pose proof (proj1 (forallb_forall _ _) Hkn K Hin) as HK. apply existsb_exists in HK as [K' [Hin' Heq]].
apply kentry_eqb_eq in Heq. subst K'. exact (proj1 (Forall_forall _ _) co_know0 K Hin').
- eapply holes_mono; [exact co_holes0 | lia].
- lia.
- lia.
- lia.
- intros a. rewrite HH. replace (in_ghost E ch) with (in_ghost E cs) by (unfold in_ghost; rewrite Hghost; reflexivity). exact (co_zero0 a).
Qed.
End SE.
#[using="Type"] Lemma ridx_lit : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "A'=&Or1uQ0%3221'H&YH&_1y5&[7r2%211%5241%711%93>14p0;1pl:@1").
Proof.
intros n Hn. unfold ridx. rewrite Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 5) with 32%Z. rewrite Z.mod_small by lia. lia.
Qed.
#[using="Type"] Lemma reg_sound : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "QC'Y='S6&R8y5'_2yR0%211%5241'@y8%611%311p061'QL'='X4r6r5r4r3r2%6554321'G&O(2%2215uQ0%4271%6231'H&Z?&_1&[7%11>%32O1%52C1&Y<r8&VNr7%221E%5241%=3Q471p0?1p0G1pl:O1pl4Q11pRFQ31pTNQ91phNQ@1pR<QB1").
Proof.
intros E cs R FULL model n HC Hn. rewrite (co_regs _ _ _ _ _ HC). unfold sr_get, reg.
assert (Hnz : bv_eqb (Z_to_bv 5 (Z.of_nat n)) 0%bv = false).
{ unfold bv_eqb. apply Z.eqb_neq. rewrite Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 5) with 32%Z. rewrite Z.mod_small by lia.
replace (bv_unsigned (0%bv : bv 5)) with 0%Z by reflexivity. lia. }
rewrite Hnz. rewrite ridx_lit by lia. reflexivity.
Qed.
#[using="Type"] Lemma lit_of_sound : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "Q4'Y='Y@'Q3'H'@%113&UGr2%211(4r1%2291%93741'G'_2yR0%211&Y<r4r3%3221&_1%127?%D3731&[3z%221C&[4&Z1%22F1%A241%B281p0D1poFO1pi@Q11pR<Q31").
Proof.
intros E e z H. destruct e; try discriminate. cbn [lit_of] in H. injection H as <-.
split; [| unfold two64; apply Z.mod_pos_bound; lia].
cbn [edenot]. apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. unfold two64.
rewrite Z.mod_mod by lia. reflexivity.
Qed.
#[using="Type"] Lemma reg_lit_sound : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "R0'Y='S6&R8y5'_2yR0%211%5241'@y8%611%311p061'QL'='Q3'X4r7r6r5r4r3%6554321'G&O(2%2215uQ0%4271%6231'H%G1@&VOr8%221>(4%12E?%73631&Z?&_1&[7%11F%32Q71%52:1%52Q7H%?3Q721&[3z%221L&[4&Z1%22O1%M241%N281p0A1p0J1p0Q21poFQ:1pl:Q<1pl4Q>1pRFQ@1pTNQF1phNQM1pR<QO1").
Proof.
intros E cs R FULL model n z HC Hn H. unfold reg_lit in H.
destruct (lit_of_sound E (reg cs n) z H) as [He Hz]. rewrite (reg_sound E cs R FULL model n HC Hn), He. auto.
Qed.
#[using="Type"] Lemma regs_ok_respell : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "Q?'Y='<'Y@%211&R8y5'_2yR0%211%5241'=&Z7r5r4r3%43321'G&O(2%2215uQ0%4271%6231'H&Y<r7%221<&Q2r6(Y2z%211%54NC41%9281%;3J81r8&YO%13<IH%K331:p051p0B1p0J1pi@Q81pl:Q11pTNQ31pmLQ:1pR<Q>1").
Proof.
intros E sr R n e HR Hn He.
replace (sr_upd sr n e) with (sr_upd sr (ridx (Z_to_bv 5 (Z.of_nat n))) e) by (rewrite ridx_lit by lia; reflexivity).
apply regs_ok_pin; [exact HR|].
rewrite (HR (Z_to_bv 5 (Z.of_nat n))). unfold sr_get.
assert (Hnz : bv_eqb (Z_to_bv 5 (Z.of_nat n)) 0%bv = false).
{ unfold bv_eqb. apply Z.eqb_neq. rewrite Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 5) with 32%Z. rewrite Z.mod_small by lia.
replace (bv_unsigned (0%bv : bv 5)) with 0%Z by reflexivity. lia. }
rewrite Hnz, ridx_lit by lia. symmetry. exact He.
Qed.
#[using="Type"] Lemma regs_ok_set_n : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "QA'Y='<'Y@%211&R8y5'_2yR0%211%5241'=&Z7r6r5r4%43321'G&O(2%2215uQ0%4271%6231'H&Y<r8%221<r3%53D21r9&YO%136CB&ZAr7&_1&[7%11H%32Q01%6351H%L3:81p0<1p0C1p0K1po0Q31pi@Q:1pl:Q31pTNQ51pmLQ<1pR<Q@1").
Proof.
intros E sr R n e v HR Hn He.
replace (sr_upd sr n e) with (sr_upd sr (ridx (Z_to_bv 5 (Z.of_nat n))) e) by (rewrite ridx_lit by lia; reflexivity).
apply regs_ok_set; [exact HR | | exact He].
intros Hz. apply (f_equal bv_unsigned) in Hz. rewrite Z_to_bv_unsigned in Hz. unfold bv_wrap in Hz.
change (bv_modulus 5) with 32%Z in Hz. rewrite Z.mod_small in Hz by lia.
replace (bv_unsigned (0%bv : bv 5)) with 0%Z in Hz by reflexivity. lia.
Qed.
#[using="Type"] Lemma fresh_ok_parts : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "QN'S6'H'7&T9v^<r1%3221(D%73621'G&WB&VIr2%211&YK&S4%114%311%8251%B3A1<&U=&U7%11:%32:1%G3F1A&UJ&S3%11?%32?1%L3K1F&VK&6'B'Y@%2211&S5%11H&S0%11J%83531%:2K1%Q83Q71Q2&T3&RN%11Q0%32Q01%Q=3Q<1Q7&T5&RO%11Q5%32Q51%QB3QA1Q<'N%12QAQ8%Q=231%Q>291%Q?2?1%Q@2L1%QA2Q21%QB2Q81p0QD1phNQM1").
Proof.
intros cs H. unfold fresh_ok in H.
repeat match type of H with (_ && _)%bool = true => apply andb_prop in H as [H ?X] end.
match goal with X : Nat.leb _ _ = true |- _ => apply Nat.leb_le in X end. repeat split; try assumption.
unfold pairs_vars_lt in *. rewrite forallb_app. apply andb_true_intro. split; assumption.
Qed.
#[using="Type"] Lemma fresh_ok_hist : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "I'S6'H'7&T9v^<r1%3221(D%73621'G&T=&VIr2%211&S2%113%6231%@3?1:&S1%117%:271%D3C1>%=251p0?1phNH1").
Proof.
intros cs H. unfold fresh_ok in H.
repeat match type of H with (_ && _)%bool = true => apply andb_prop in H as [H ?X] end.
split; assumption.
Qed.
#[using="Type"] Lemma hreplay_agree : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "Q1'='Y='<'T?%211&Z9r4r3r2%43321'H'7&T=r5%2216(D%63521'B'_2yR0%211%4211%D11&X<%12BA%22<B%@3421p0;1p0C1pj8I1pR>M1pR<N1pgFQ01").
Proof.
intros b E E' h Hag. induction h as [|[hb hn|hb hn] h IH]; intros Hv; [reflexivity| |];
cbn [hist_vars_lt forallb hop_b hop_n] in Hv; apply andb_prop in Hv as [H1 Hl]; apply andb_prop in H1 as [H1 H2];
cbn [hreplay]; rewrite (IH Hl); unfold uE;
rewrite <- (edenot_agree' b E E' _ Hag H1), <- (edenot_agree' b E E' _ Hag H2); reflexivity.
Qed.
#[using="Type"] Lemma allowA_agree : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "Q6'='Y='S6&Z9r4r3r2%43321'H'7&VKr5&6'B'Y@%2211&S5%11;&S0%11=%83531%;2:1(D%?3>21'<'Q3%=211%311&X2%12IH%22CI%G3421p091p0J1phNQ01pR>Q21pR<Q31pgFQ51").
Proof.
intros b E E' cs Hag H. unfold allowA. rewrite !flat_map_concat_map. f_equal. apply map_ext_in. intros p Hin.
pose proof (proj1 (forallb_forall _ _) H p Hin) as Hp. apply andb_prop in Hp as [H1 H2].
unfold allow1, sh_lo, sh_hi, uE. rewrite <- (edenot_agree' b E E' _ Hag H1), <- (edenot_agree' b E E' _ Hag H2). reflexivity.
Qed.
Section SE.
Local Abbreviation SEC_T_in_allow_agree := (ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "M'='Y='S6&Z9r4r3r2%43321'H'7&VKr5&S5%117%4231(D%83721'Q3poF19&X=%12@?%22:@%>3421p071p0A1phNG1pR>I1pR<J1pgFL1")) (only parsing).
Variable b : ltac:(sec_ty2 constr:(SEC_T_in_allow_agree) 0%nat 0%nat).
Variable E : ltac:(sec_ty2 constr:(SEC_T_in_allow_agree) 1%nat 0%nat).
Variable E' : ltac:(sec_ty2 constr:(SEC_T_in_allow_agree) 2%nat 0%nat).
Variable cs : ltac:(sec_ty2 constr:(SEC_T_in_allow_agree) 3%nat 0%nat).
Lemma in_allow_agree : ltac:(sec_stmt2 constr:(SEC_T_in_allow_agree) 4%nat 0%nat).
Proof using Type b E E' cs.
intros Hag H.
apply functional_extensionality. intros z. unfold in_allow, in_vis, in_sh. unfold pairs_vars_lt in H.
induction (a_vis cs) as [|p l IH]; [reflexivity|]. cbn [existsb forallb] in H |- *.
apply andb_prop in H as [Hp Hl]. apply andb_prop in Hp as [H1 H2].
unfold sh_lo, sh_hi, uE in *. rewrite <- (edenot_agree' b E E' _ Hag H1), <- (edenot_agree' b E E' _ Hag H2).
pose proof (IH Hl) as E1. apply (f_equal negb) in E1. rewrite !negb_orb in E1.
apply (f_equal negb) in E1. rewrite !negb_andb, !negb_involutive in E1.
destruct (existsb _ l), (existsb _ l), (existsb _ l), (existsb _ l); cbn in E1 |- *; rewrite ?orb_true_r, ?orb_false_r; try reflexivity; try discriminate.
Qed.
End SE.
#[using="Type"] Lemma in_ghost_agree : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "Q4'='Y='S6&Z9r4r3r2%43321'H'7&VKr5&6'B'Y@%2211&S5%11;&S0%11=%83531%;2:1(D%?3>21'Q3poF1@&X>%12GF%22AG%E3421p071p0H1phNN1pR>Q01pR<Q11pgFQ31").
Proof.
intros b E E' cs Hag H. apply functional_extensionality. intros z. unfold in_ghost.
unfold pairs_vars_lt in H. rewrite forallb_app in H. apply andb_prop in H as [_ H].
induction (a_ghost cs) as [|p l IH]; [reflexivity|]. cbn [existsb forallb] in H |- *.
apply andb_prop in H as [Hp Hl]. apply andb_prop in Hp as [H1 H2].
unfold uE in *. rewrite <- (edenot_agree' b E E' _ Hag H1), <- (edenot_agree' b E E' _ Hag H2), (IH Hl). reflexivity.
Qed.
#[using="e_sp0_init"] Lemma utop_agree : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "F'='Y=&Z9r3r2r1%43321'Nv^<r4%3221'H'Q3&XJ%11;%216%53421p071p0<1pR>B1pR<C1pgFE1").
Proof.
intros b E E' Hag Hle. unfold utop, uE.
rewrite (edenot_agree' nx0 E E' e_sp0 (env_agree_le _ _ _ _ Hag Hle) e_sp0_init). reflexivity.
Qed.
#[using="Type"] Lemma e_sppg_vars : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "?'='H'7&T3r1&SL%3221(D%73621r2&SM%8221%;3:15p051pl:>1").
Proof. intros n H. vm_compute in H. vm_compute. do 11 (destruct n as [|n]; [cbn in H; discriminate|]). reflexivity. Qed.
#[using="e_sp0_init"] Lemma sppg_agree : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "G'='Y=&Z9r3r2r1%43321'Nv^<r4%3221'H'Q3&Y1&SM%22<1%3272%63521p081p0=1pR>C1pR<D1pgFF1").
Proof.
intros b E E' Hag Hle. unfold uE.
rewrite (edenot_agree' nx0 E E' e_sppg (env_agree_le _ _ _ _ Hag Hle) (e_sppg_vars nx0 e_sp0_init)). reflexivity.
Qed.
#[using="e_sp0_init argH_agree"] Lemma hid_agree : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "Q='='Y='S6'QL&Z9r5r4r3%43321'Nv^<r6%3221'H'7&VKr7&6'B'Y@%2211&S5%11@&S0%11B%83531%;2:1(D%?3>21'_2yR0%211pg@1B&X:%13GML%23CNM%G3421p091p0J1p0O1pl4Q51phNQ71pR>Q91pR<Q:1pgFQ<1").
Proof.
intros b E E' cs model Hag Hle H. apply functional_extensionality. intros a. unfold hid, vis.
assert (H' : pairs_vars_lt b (a_vis cs) = true).
{ unfold pairs_vars_lt in *. rewrite forallb_app in H. apply andb_prop in H as [H _]. exact H. }
rewrite (in_allow_agree b E E' cs Hag H'). rewrite (argH_agree E E' a) by (eapply env_agree_le; eassumption).
rewrite (utop_agree b E E' Hag Hle). reflexivity.
Qed.
#[using="Type"] Lemma maps_den_agree : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "Q4'='Y='<'S<%211&Z9r4r3r2%43321'H'7&UJr5%2216(D%63521'B'_2yR0%211%4211%D11&Q1&X3%11C%34G51C%31>%54I71E%C3731p0>1p0F1pl8L1pR>Q01pR<Q11pgFQ31").
Proof.
intros b E E' ms Hag H. apply map_ext_in. intros m Hin.
pose proof (proj1 (forallb_forall _ _) H m Hin) as Hm. apply andb_prop in Hm as [H1 H2].
unfold amap_den. rewrite <- (edenot_agree' b E E' _ Hag H1), <- (edenot_agree' b E E' _ Hag H2). reflexivity.
Qed.
#[using="Type"] Lemma maps_match_agree : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "Q2'='Y='<'S<%211'B'_2yR0%211%4211%811&Z9r5r4r3%43321'H'7&UJr6%2216(D%63521&XD%135;:%236=<p021p051p0=1pk<C1pl8J1pR>N1pR<O1pgFQ11").
Proof.
intros b E E' ms. induction ms as [|m ms IH]; intros l Hag H HM; cbn [maps_match] in *; [exact HM|].
cbn [maps_vars_lt forallb] in H. apply andb_prop in H as [Hm Hr]. apply andb_prop in Hm as [H1 H2].
unfold uE, amap_den in *. rewrite <- (edenot_agree' b E E' _ Hag H1), <- (edenot_agree' b E E' _ Hag H2).
destruct (is_fog m).
- destruct HM as [HM|(iv & l' & -> & Hsz & HM)]; [left; exact (IH _ Hag Hr HM) | right].
exists iv, l'. split; [reflexivity|]. split; [exact Hsz | exact (IH _ Hag Hr HM)].
- destruct HM as (l' & -> & HM). exists l'. split; [reflexivity | exact (IH _ Hag Hr HM)].
Qed.
#[using="Type"] Lemma holes_agree : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "Q9'='Y='Q3'<'B'_2yR0%211%4211%611'S<%811&Z9r6r5r4%43321'H'7&UJr7r2%3221(D%73621'Q0&X;%137=<r3%43C21%43:A@%63E1@p031p091p0B1pl8H1pk<K1po@Q31pR>Q51pR<Q61pgFQ81").
Proof.
intros b E E' y l ms Hag Hv H. apply Forall_forall. intros m Hin Hh.
pose proof (proj1 (forallb_forall _ _) Hv m Hin) as Hm. apply andb_prop in Hm as [H1 H2].
unfold hole_ok, uE in *. rewrite <- (edenot_agree' b E E' _ Hag H1), <- (edenot_agree' b E E' _ Hag H2).
exact (proj1 (Forall_forall _ _) H m Hin Hh).
Qed.
#[using="Type"] Lemma fds_ok_agree : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "K'='Y='S8'QL&Z9r5r4r3%43321'H'7&T5r6%2216(D%63521&X7%135;:%236=<p021p051p0=1pl4C1piJE1pR>G1pR<H1pgFJ1").
Proof.
intros b E E' f model Hag Hv H. destruct f as [|k len off|]; try exact H.
cbn [fd_vars_lt] in Hv. apply andb_prop in Hv as [Hl Ho].
destruct H as [p [c (H1 & H2 & H3 & H4 & H5)]]. exists p, c.
unfold uE in *. rewrite <- (edenot_agree' b E E' _ Hag Hl), <- (edenot_agree' b E E' _ Hag Ho).
destruct Hag as [_ Heb]. rewrite <- Heb. repeat split; assumption.
Qed.
#[using="e_sp0_init argH_agree SINV_agree"] Lemma cs_ok_agree : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "Q;'Y='S6&R8y5'_2yR0%211%5241'@y8%611%311p061'QL&Z9&VIr4%211r6r5%63321'H'7&T9v^<%2216(D%63521'X4r8r3%352=<?1r7%5541?>Ap031p081p0@1pl4H1pRFJ1pTNQ01phNQ71pR>Q91pR<Q:1").
Proof.
intros E E' cs R FULL model Hag Hf HC.
destruct (fresh_ok_parts cs Hf) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
pose proof (hid_agree (nxt cs) E E' cs model Hag Fle Fallow) as HH.
pose proof (allowA_agree (nxt cs) E E' cs Hag Fallow) as HA.
pose proof (utop_agree (nxt cs) E E' Hag Fle) as HU.
assert (HSP : uE E' e_sp0 = uE E e_sp0).
{ unfold uE. rewrite (edenot_agree' nx0 E E' e_sp0 (env_agree_le _ _ _ _ Hag Fle) e_sp0_init). reflexivity. }
pose proof (sppg_agree (nxt cs) E E' Hag Fle) as HSG.
destruct HC; constructor; rewrite ?HA, ?HSP, ?HSG; try assumption.
- eapply regs_ok_agree'; eassumption.
- unfold Mr. rewrite HH. eapply know_ok_agree'; eassumption.
- eapply fds_ok_agree; eassumption.
- eapply maps_match_agree; [exact Hag | exact Fmaps | assumption].
- eapply holes_agree; [exact Hag | exact Fmaps | assumption].
- eapply Forall_impl; [|exact co_bounds0]. intros iv Hiv. cbv beta in Hiv. rewrite HU. exact Hiv.
- eapply Forall_impl; [|exact co_lazyb0]. intros iv Hiv. cbv beta in Hiv. rewrite HU. exact Hiv.
- apply Forall_forall. intros m Hin Hk.
pose proof (proj1 (forallb_forall _ _) Fmaps m Hin) as Hm. apply andb_prop in Hm as [H1 H2].
unfold amap_den. rewrite <- (edenot_agree' (nxt cs) E E' _ Hag H1), <- (edenot_agree' (nxt cs) E E' _ Hag H2).
exact (proj1 (Forall_forall _ _) co_none0 m Hin Hk).
- apply Forall_forall. intros m Hin Hk a Ha.
pose proof (proj1 (forallb_forall _ _) Fmaps m Hin) as Hm. apply andb_prop in Hm as [H1 H2].
rewrite <- (edenot_agree' (nxt cs) E E' _ Hag H1), <- (edenot_agree' (nxt cs) E E' _ Hag H2) in Ha.
exact (proj1 (Forall_forall _ _) co_kinds0 m Hin Hk a Ha).
- rewrite <- (edenot_agree' (nxt cs) E E' _ Hag Fbrk). assumption.
- intros a. rewrite HH, (in_ghost_agree (nxt cs) E E' cs Hag Fallow). exact (co_zero0 a).
- eapply SINV_agree; [eapply env_agree_le; [exact Hag | exact Fle] | assumption].
- destruct (fresh_ok_hist cs Hf) as [F1 F2]. unfold RNA. rewrite (hreplay_agree (nxt cs) E E' _ Hag F1). assumption.
- destruct (fresh_ok_hist cs Hf) as [F1 F2]. unfold RLZ. rewrite (hreplay_agree (nxt cs) E E' _ Hag F2). assumption.
Qed.
#[using="Type"] Lemma fresh_ok_mono : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "C'='S6'Nv^<r2%3221'H'7&T9r3%2216(D%63521%52:4%83713p031p0;1phN@1pj4B1").
Proof.
intros gb cs Hle H. unfold fresh_ok in *.
repeat match type of H with (_ && _)%bool = true => apply andb_prop in H as [H ?X] end.
match goal with X : Nat.leb _ _ = true |- _ => apply Nat.leb_le in X end.
repeat (apply andb_true_intro; split); try assumption. apply Nat.leb_le. lia.
Qed.
#[using="IT_ok HS XN XE XB SEGS_wx SEGS_in_hull HULL_ok argH_high e_sp0_init argH_agree SINV_frame SINV_agree"] Lemma run_block_sound : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "RK'='<'Q3%211'S6'Y=&R8y5'_2yR0%211%5241'@y8%611%311p061'QL&ZC'Nv^<r:%3221'H%<1D&W4vZJvQAr;vQDr9r8%776543;21(4r7%22O1%=3<41'X4r6r5r4%457;321'G&Z9r<%23I15&VIr>%211%63159%8251r3r2%@5>6=21&QF&QN%115%21M%Q33421'ZHv^I&XL&VLr@%211%45Q7K1JI%74Q861Q6p091p0?1p0C1pl6QE1pRHQG1pU0QM1pR>R41%<1Q>%>5QAQ<1Q9Q5%A4QB@1Q5p041p0Q51p0Q;1p0QJ1pfHQO1pl4R11pRFR31pTNR91pR<R@1pi0RB1phNRC1pn<RE1pgNRI1pj4RJ1").
Proof.
intros gb bfuel stops cs cs' E R FULL model T Hgb Hrb HC Hk.
rewrite run_block_eq in Hrb. unfold run_block_ref in Hrb.
destruct (fresh_ok gb cs) eqn:Hf0; [|discriminate].
pose proof (fresh_ok_mono gb cs Hgb Hf0) as Hf.
destruct (fresh_ok_parts cs Hf) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
pose proof (co_regs _ _ _ _ _ HC) as HR. pose proof (co_know _ _ _ _ _ HC) as HK.
unfold kn in HK, Fkn. unfold nxt in Fsr, Fkn, Fmaps, Fallow, Fbrk, Ffd, Fle, Hk.
destruct (a_ss cs) as [p sr log k nx rsv] eqn:Hss.
cbn [s_know s_regs s_pc s_next] in Hrb, HR, HK, Fsr, Fkn, Fmaps, Fallow, Fbrk, Ffd, Fle, Hk.
set (ss' := sym_execTX SEGS IT KC bfuel true stops (SS p sr [] k nx)) in Hrb.
destruct (carry (s_log ss') (s_know ss') []) as [[kn' scs] hs] eqn:Hc.
destruct scs; [|discriminate]. injection Hrb as <-.
set (H := hid E cs model). set (MR := Mr E cs model FULL).
rewrite sr_vars_lt_eq in Fsr. rewrite kn_vars_lt_eq in Fkn.
pose proof (runTX_sound SEGS IT KC bfuel stops p sr k nx E MR (seg_rom SEGS) R IT_ok HR HK Fsr Fkn) as HX.
cbn zeta in HX. fold ss' in HX. destruct HX as (E' & R' & Hag & Hle & HR' & Hlf & HK' & Hms & _).
assert (Hagc : env_agree (nxt cs) E E') by (unfold nxt; rewrite Hss; exact Hag).
pose proof (cs_ok_agree E E' cs R FULL model Hagc Hf HC) as HC'.
assert (HH : hid E' cs model = H).
{ unfold H. eapply hid_agree; [exact Hagc | unfold nxt; rewrite Hss; exact Fle | unfold nxt; rewrite Hss; exact Fallow]. }
unfold cfg_of, pc. rewrite Hss. cbn [a_ss s_pc].
apply (srz_msteps_restricted_T SEGS scfg H (H_off_segments_cs E cs model) SEGS_wx (allowA E cs)
(mkst R (Z_to_bv 64 p) FULL (seg_rom SEGS)) _ model T
(lazy_cover_cs E cs R FULL model HC) (A_wf_allowA E cs) (co_minv _ _ _ _ _ HC) (co_halt _ _ _ _ _ HC) Hms).
intros model' Hinv' Hsame Hclean.
assert (HKc : know_ok SEGS E' (mem_denot E' MR (s_log ss')) kn').
{ eapply (carry_sound SEGS E' MR); [exact Hc | exact Hlf | exact HK' | constructor]. }
set (FULL' := munrestrict H FULL (mem_denot E' MR (s_log ss'))).
assert (Hmr' : Mr E' cs model FULL' = mem_denot E' MR (s_log ss')).
{ unfold Mr, FULL'. rewrite HH. apply mrestrict_munrestrict_clean. intros a Ha. exact (Hclean a Ha). }
assert (Flec : (nx0 <= nxt cs)%nat) by (unfold nxt; rewrite Hss; exact Fle).
assert (Fallowc : pairs_vars_lt (nxt cs) (a_vis cs ++ a_ghost cs) = true) by (unfold nxt; rewrite Hss; exact Fallow).
specialize (Hk E' R' FULL' model' (conj (env_agree_le _ _ _ _ Hag Fle) Hag)).
unfold cfg_of, pc in Hk. cbn [with_ss a_ss mk_ss s_pc] in Hk.
replace (unrestrict H (ms_mem (mkst R (Z_to_bv 64 p) FULL (seg_rom SEGS)))
(mkst R' (Z_to_bv 64 (s_pc ss')) (mem_denot E' MR (s_log ss')) (seg_rom SEGS)))
with (mkst R' (Z_to_bv 64 (s_pc ss')) FULL' (seg_rom SEGS)) by reflexivity.
apply Hk.
- eapply cs_ok_frame; [exact HC' | exact Hsame | | exact HR' | reflexivity | | ].
+ rewrite (allowA_agree (nxt cs) E E' cs Hagc Fallowc). exact Hinv'.
+ cbn [mk_ss s_know]. rewrite Hmr'. exact HKc.
+ intros a Ha. rewrite HH in Ha. unfold FULL', munrestrict. rewrite Ha. reflexivity.
- pose proof (same_but_materialized_frame _ _ Hsame) as Hfr. apply Hfr.
Qed.
#[using="IT_ok HS XN XE XB SEGS_wx SEGS_in_hull HULL_ok argH_high e_sp0_init argH_agree SINV_frame SINV_agree"] Lemma run_block_gc_sound : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "RK'='<'Q3%211'S6'Y=&R8y5'_2yR0%211%5241'@y8%611%311p061'QL&ZC'Nv^<r:%3221'H%<1D&W5vZJvQAr;vQDr9r8%776543;21(4r7%22O1%=3<41'X4r6r5r4%457;321'G&Z9r<%23I15&VIr>%211%63159%8251r3r2%@5>6=21&QF&QN%115%21M%Q33421'ZHv^I&XL&VLr@%211%45Q7K1JI%74Q861Q6p091p0?1p0C1pl6QE1pRHQG1pU0QM1pR>R41%<1Q>%>5QAQ<1Q9Q5%A4QB@1Q5p041p0Q51p0Q;1p0QJ1pfHQO1pl4R11pRFR31pTNR91pR<R@1pi0RB1phNRC1pn<RE1pgNRI1pj4RJ1").
Proof.
intros gb bfuel stops cs cs' E R FULL model T Hgb H HC Hk. unfold run_block_gc in H.
destruct (run_block SEGS IT gb KC bfuel stops cs) as [cs1|] eqn:Hrb; [|discriminate]. injection H as <-.
eapply run_block_sound; [exact Hgb | exact Hrb | exact HC |].
intros E' R' FULL' model' Hag HC1 Hfs. rewrite <- (pc_cs_gc gb cs1). apply (Hk E' R' FULL' model'); [exact Hag | apply cs_gc_ok; exact HC1 | exact Hfs].
Qed.
#[using="Type"] Lemma u_small : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "G'Q3'G&[3zr1%3221&[4&[9+2+R0%3221%5271%;271'H&_3yR0&_1r2%2231%5241%73D13p091poFF1").
Proof. intros. apply u64_lit. assumption. Qed.
#[using="Type"] Lemma nth_sr_vars_lt : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "N'='<'Y@%211'H'7&WBr3r2%3221(D%73621&OuQ0%2261&T3r5&Q2r4(Y2z%211%54D?41%8271%D3C1>p0;1p0?1pm:K1pmLI1pgFM1").
Proof.
intros b sr. induction sr as [|x t IH]; intros r H Hr; [destruct r; reflexivity|].
cbn [APK.sr_vars_lt] in H. apply andb_prop in H as [H1 H2]. destruct r as [|r]; [exact H1|]. cbn [nth]. apply IH; [exact H2 | lia].
Qed.
#[using="e_sp0_init argH_agree SINV_agree"] Lemma node_fresh_sound_pf : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "1&X8").
Proof.
intros r logc base cs cs' E R FULL model T HC _ Hn Hk. cbv beta in Hn. unfold node_fresh in Hn.
set (b := match base with Some b => b | None => ELit 0 end) in Hn.
set (e := esub (reg cs r) b) in Hn.
destruct (Nat.ltb 0 r && Nat.ltb r 32 && Z.leb 0 logc && Z.leb logc 40 && Z.leb logc (ealign (kn cs) e)
&& APK.expr_vars_lt (nxt cs) b && APK.expr_vars_lt (nxt cs) e && fresh_ok nx0 cs)%bool eqn:Hc; [|discriminate].
apply andb_prop in Hc as [Hc Hfresh]. apply andb_prop in Hc as [Hc Hve]. apply andb_prop in Hc as [Hc Hvb].
apply andb_prop in Hc as [Hc Hal]. apply andb_prop in Hc as [Hc H40]. apply andb_prop in Hc as [Hc H0].
apply andb_prop in Hc as [Hr0 Hr32].
apply Nat.ltb_lt in Hr0. apply Nat.ltb_lt in Hr32. apply Z.leb_le in H0. apply Z.leb_le in H40. apply Z.leb_le in Hal.
destruct (xlo2 (kn cs) e) as [lo|] eqn:Hlo; [|discriminate].
destruct (xhi2 (kn cs) e) as [hi|] eqn:Hhi; [|discriminate].
injection Hn as <-.
set (c := 2 ^ logc) in *. set (v := nxt cs) in *.
pose proof (co_know _ _ _ _ _ HC) as HK.
pose proof (xlo2_sound E _ (kn cs) e lo HK Hlo) as Hlo'.
pose proof (xhi2_sound E _ (kn cs) e hi HK Hhi) as Hhi'.
destruct (ealign_sound SEGS E _ (kn cs) e HK) as [Hea Hdiv].
assert (Hc : 0 < c) by (unfold c; apply Z.pow_pos_nonneg; lia).
assert (Hc2 : c <= 2 ^ 40) by (unfold c; apply Z.pow_le_mono_r; lia).
assert (Hcd : (c | bv_unsigned (edenot E e))%Z).
{ eapply Z.divide_trans; [|exact Hdiv]. unfold c. apply pow2_divide_le. lia. }
destruct Hcd as [q Hq].
pose proof (u64_range (edenot E e)) as Hue.
assert (Hq0 : 0 <= q) by nia.
assert (Hq64 : q < 2 ^ 64) by nia.
set (a := Z_to_bv 64 q). set (E' := ext1 E v a).
assert (Hag : env_agree v E E') by apply ext1_agree.
destruct (fresh_ok_parts cs Hfresh) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
pose proof (cs_ok_agree E E' cs R FULL model Hag Hfresh HC) as HC'.
assert (Hev : edenot E' e = edenot E e) by (symmetry; eapply (edenot_agree' v); [exact Hag | exact Hve]).
assert (Hbv : edenot E' b = edenot E b) by (symmetry; eapply (edenot_agree' v); [exact Hag | exact Hvb]).
assert (Hrv : edenot E' (reg cs r) = edenot E (reg cs r)).
{ symmetry. eapply (edenot_agree' v); [exact Hag|]. unfold reg. apply nth_sr_vars_lt; [exact Fsr | lia]. }
assert (Hne : edenot E' (escale c (EVar v)) = edenot E e).
{ unfold escale. rewrite mkMd_denot. cbn [edenot]. unfold E'. rewrite ext1_at. unfold a.
apply bv_eq. rewrite u_mul64. rewrite (u_small c) by lia. rewrite (u_small q) by lia. rewrite Z.mod_small by nia. lia. }
assert (He_sem : edenot E e = alu64 ALU_SUB (edenot E (reg cs r)) (edenot E b)) by (unfold e, esub; apply mkAlu_denot).
apply (Hk E' R FULL model); [split; [eapply env_agree_le; [exact Hag | exact Fle] | exact Hag] | | reflexivity].
assert (HKf : know_ok SEGS E' (Mr E' cs model FULL)
((KRange (EVar v) ((lo + c - 1) / c) (hi / c) :: KRange (esub e (escale c (EVar v))) 0 0
:: residue_fact (kn cs) e (escale c (EVar v)))
++ kn cs)).
{ apply Forall_app. split; [|exact (co_know _ _ _ _ _ HC')].
constructor; [|constructor].
- cbn [kentry_ok edenot]. unfold E' at 1 2. rewrite ext1_at. unfold a. rewrite u_small by lia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
split; nia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
- cbn [kentry_ok]. unfold esub. rewrite !mkAlu_denot, !Hne, !Hev.
rewrite !u_sub64. rewrite Z.sub_diag, Z.mod_0_l by lia. lia.
- eapply (residue_fact_sound E E' _ _ (kn cs) e); [exact HK | exact Hne |].
intros e1 s1 Hd1. symmetry. eapply (edenot_agree' v); [exact Hag | exact (deand_vars v e e1 s1 Hd1 Hve)]. }
destruct HC'; constructor; cbn [bump set_reg add_kn set_kn with_ss a_ss mk_ss s_regs s_log s_know kn a_maps a_totsz a_ylo a_eager a_vis a_abytes a_brk a_fd a_tidset a_hna a_hlz]; try assumption.
- apply regs_ok_respell; [exact co_regs0 | lia |].
unfold eadd. rewrite mkAlu_denot, Hne, Hbv. fold (reg cs r). rewrite Hrv, He_sem.
apply bv_eq. rewrite u_add64, u_sub64. pose proof (u64_range (edenot E (reg cs r))). pose proof (u64_range (edenot E b)).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
rewrite Zplus_mod_idemp_r. replace (bv_unsigned (edenot E b) + (bv_unsigned (edenot E (reg cs r)) - bv_unsigned (edenot E b))) with (bv_unsigned (edenot E (reg cs r))) by lia.
rewrite Z.mod_small by lia. reflexivity.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
- reflexivity.
Qed.
#[using="Type"] Lemma listZ_eqb_eq : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "@'<'Q3%211'H'7&UDr2r1%3221(D%73621r3%93:16p031po@<1po>=1").
Proof.
induction x as [|a x IH]; intros [|b y] H; cbn [listZ_eqb] in H; try discriminate; [reflexivity|].
apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1. rewrite (IH y H2), H1. reflexivity.
Qed.
#[using="Type"] Lemma spieces_eqb_eq : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "@'<'W?%211'H'7&W@r2r1%3221(D%73621r3%93:16p031po@<1po>=1").
Proof.
induction x as [|a x IH]; intros [|b y] H; cbn [spieces_eqb] in H; try discriminate; [reflexivity|].
apply andb_prop in H as [H1 H2]. rewrite (IH y H2). f_equal.
destruct a as [l|k], b as [l'|k']; cbn [spiece_eqb] in H1; try discriminate.
- apply listZ_eqb_eq in H1. congruence.
- apply Nat.eqb_eq in H1. congruence.
Qed.
#[using="Type"] Lemma shape_eqb_eq : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK ">'W<'H'7&W=r2r1%3221(D%73621r3%93:16p031po@<1po>=1").
Proof.
induction x; intros y H; destruct y; cbn [shape_eqb] in H; try discriminate;
repeat match type of H with (_ && _)%bool = true => apply andb_prop in H as [H ?X] end; try reflexivity.
- apply Z.eqb_eq in H. congruence.
- apply Z.eqb_eq in H. apply spieces_eqb_eq in X0. rewrite (IHx _ X). congruence.
- rewrite (IHx1 _ H), (IHx2 _ X). reflexivity.
- apply expr_eqb_eq in H. apply Z.eqb_eq in X1. rewrite (IHx1 _ X0), (IHx2 _ X). congruence.
- apply Nat.eqb_eq in H. congruence.
Qed.
Section SE.
Local Abbreviation SEC_T_find_disj_sound := (ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "R='Y='_2yR0%211'@y8%511%311p051'<'YE%211'Y@'Q3&Z6vZJr;r:r9%544321'H'B%12:9%221;%321<%421<%521>%G11&T6r8%23=<1(4(Ar7r6%34GF21r5%54?I21r4%74@K21r3%94AL21r2%;4BO21%=2B1%I3B?1'L&[3&[1&Z4r=(Y8%12GC%4231&Z3%125E%8231%62EC%9281%<231%62:D%=231%?219%A241p0C1p0Q>1pl>QF1pm0QF1ph>QH1pl<QI1plNQI1ph<QK1pgLQL1pgJQM1pk0QO1pTDR31pR<R<1")) (only parsing).
Variable E : ltac:(sec_ty2 constr:(SEC_T_find_disj_sound) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_find_disj_sound) 1%nat 0%nat).
Lemma find_disj_sound : ltac:(sec_stmt2 constr:(SEC_T_find_disj_sound) 2%nat 0%nat).
Proof using Type E M.
intros k b1 b2 c1 o1 n1 c2 o2 n2 HK.
induction k as [|K k IH]; intros H; [discriminate|].
inversion HK as [|K' k' HKK HK']; subst.
cbn [find_disj] in H.
destruct K as [| | | | | | |[d1 p1] m1 [d2 p2] m2| |]; try exact (IH HK' H).
destruct (expr_eqb d1 b1 && expr_eqb d2 b2)%bool.
- injection H as <- <- <- <- <- <-. exact HKK.
- destruct (expr_eqb d1 b2 && expr_eqb d2 b1)%bool; [|exact (IH HK' H)].
injection H as <- <- <- <- <- <-. cbn [kentry_ok] in HKK. lia.
Qed.
End SE.
#[using="Type"] Lemma disj_side_fact_sound : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "R='Y='_2yR0%211'@y8%511%311p051'<'YE%211'Y@'Q3&Z6vZJr9r8r7%544321'H%A1;&SIr6r5r4r3%56:94321(4r2%22D1%;3:41&[3z&Z4r;(Y8%12DC%4231%7261&[4r<%62CB%9221&[9+2+R0%3221%8251&[1r=r:%@21Q4%C231&Z3%125Q6%7231%E2Q7Q2%H281%K231&Z5r>%24Q?1<Q7p041p0@1p0J1p0Q31p0Q@1pS8QJ1pm4QH1phBQJ1pl@QK1pm2QK1ph@QM1pk0QO1pTDR31pR<R<1").
Proof.
intros E M k cA oA nA cB oB K HK H HA HB Hle. unfold disj_side_fact in H.
destruct (xlo2 k nA) as [n|] eqn:Hn; [|discriminate].
destruct (base_range k cB) as [[blo bhi]|] eqn:Hbr; [|discriminate].
destruct (Z.leb 0 n && Z.leb n (bhi + oB))%bool eqn:Ht; [|discriminate]. injection H as <-.
apply andb_prop in Ht as [H0 H1]. apply Z.leb_le in H0. apply Z.leb_le in H1.
pose proof (xlo2_sound E M k nA n HK Hn) as Ln. pose proof (base_range_sound SEGS E M k cB blo bhi HK Hbr) as [_ Bh].
pose proof (u64_range (edenot E nA)) as RnA.
cbn [kentry_ok]. unfold esub, eaddz. rewrite !mkAlu_denot, u_sub64, !u_add64. cbn [edenot]. rewrite !u_lit64.
unfold estart, elenZ in *; cbn [a_base a_off] in *.
pose proof (u64_range (edenot E cA)) as RA. pose proof (u64_range (edenot E cB)) as RB. unfold two64.
set (uA := bv_unsigned (edenot E cA)) in *. set (uB := bv_unsigned (edenot E cB)) in *. set (uN := bv_unsigned (edenot E nA)) in *.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
assert (E1 : (uB + oB mod 2 ^ 64) mod 2 ^ 64 = uB + oB).
{ rewrite Zplus_mod_idemp_r. apply Z.mod_small. lia. }
assert (E2 : (uA + oA mod 2 ^ 64) mod 2 ^ 64 = uA + oA).
{ rewrite Zplus_mod_idemp_r. apply Z.mod_small. lia. }
rewrite E1, E2. rewrite Z.mod_small by lia. lia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.
#[using="Type"] Lemma scaled_var_cases : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "Q='Y@'Q3'='H'@'B%1254%311&W7r3%211(4(Ar2r1%34>=21%52:1%>3:71'L'Gr4(Y4%119%D3G31+1%F3H@1%7231(Y3(R5(Y2%11E%43319%M3Q0<1&[4z%221J&Z1%42L1%C231%D271%F2>1p0H1po0Q81ph:Q:1pi@Q<1").
Proof.
intros e c v H. destruct e as [z|n|op a b|op a b|op a b|op a b|sx lo n e|sx k i n]; cbn [scaled_var] in H; try discriminate.
- left. injection H as E1 E2. subst. auto.
- destruct op; try discriminate. destruct a as [c'| | | | | | |]; try discriminate. destruct b as [|v'| | | | | |]; try discriminate.
destruct (Z.ltb 0 c' && Z.ltb c' two64)%bool eqn:Hc; [|discriminate]. injection H as E1 E2. subst.
apply andb_prop in Hc as [Hc1 Hc2]. apply Z.ltb_lt in Hc1. apply Z.ltb_lt in Hc2. right. auto.
Qed.
#[using="Type"] Lemma scaled_var_sound : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "Q@'Y@'Q3'='H'@'B%1254%311&W7r3%211(4(Ar2r1%34>=21%52:1%>3:71'G&[4z%221<'Y=&_3yR0&Y<r5%22=1%5241&[5&[6r4&Y?%12CH%;2:1%5241&[9+2+R0%3221%;251%Q63Q8=1pR<D1%I2F1p0K1po0Q;1ph:Q=1pi@Q?1").
Proof.
intros e c v H. destruct (scaled_var_cases e c v H) as [[-> ->] | [-> Hc]].
- split; [lia|]. intros E. cbn [edenot]. pose proof (u64_range (ev E v)). rewrite Z.mod_small; lia.
- unfold two64 in Hc. split; [lia|]. intros E. cbn [edenot]. rewrite u_mul64, u_lit64. unfold two64. rewrite (Z.mod_small c) by lia. reflexivity.
Qed.
#[using="Type"] Lemma div_lower : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "G'Q3&[4zr2%3221&[3r4&[6r3%2216%5241&[8&[2r5%311%3219%511%<219p081p0?1pg4D1ph:E1pg6F1").
Proof.
intros X c V Hc H.
assert (AA : (- (c * V)) / c <= (- X) / c) by (apply Z.div_le_mono; lia).
replace (- (c * V)) with ((- V) * c) in AA by lia. rewrite Z.div_mul in AA by lia. lia.
Qed.
#[using="Type"] Lemma div_upper : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "D'Q3&[4zr2%3221&[3&[6r3%2215r4%5221&[2r5%2214%9271p051p0<1pg4A1ph:B1pg>C1").
Proof.
intros Y c V Hc H.
assert (AA : (c * V) / c <= Y / c) by (apply Z.div_le_mono; lia).
replace (c * V) with (V * c) in AA by lia. rewrite Z.div_mul in AA by lia. lia.
Qed.
Section SE.
Local Abbreviation SEC_T_disj_var_fact_sound := (ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "QF'Y='_2yR0%211'@y8%511%311p051'<'YE%211'Y@'Q3&Z6vZJr8r7r6%544321&[3&[1&Z4r9(Y8r5%2281%5241&Z3r4%2271%:241r3r2%:221%=2<1%@251'Q0&Z5r:%23I1A&SJ%16JIHA=:%63Q131p081p0J1pm4Q11phBQ31pl@Q41pm2Q41ph@Q61pk0Q81pTDQ<1pR<QE1")) (only parsing).
Variable E : ltac:(sec_ty2 constr:(SEC_T_disj_var_fact_sound) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_disj_var_fact_sound) 1%nat 0%nat).
Variable k : ltac:(sec_ty2 constr:(SEC_T_disj_var_fact_sound) 2%nat 0%nat).
Lemma disj_var_fact_sound : ltac:(sec_stmt2 constr:(SEC_T_disj_var_fact_sound) 3%nat 0%nat).
Proof using Type E M k.
intros cA oA nA cB oB HK Hle.
unfold disj_var_fact.
unfold estart, elenZ in Hle. cbn [a_base a_off] in Hle.
assert (CASE2 : Forall (kentry_ok SEGS E M)
(match scaled_var cA, cB with
| Some (c, v), ELit b =>
match xlo k (EVar v), xhi k (EVar v), xlo2 k nA with
| Some vlo, Some vhi, Some nlo =>
let hi := (b + oB - oA - nlo) / c in
if (Z.leb 0 b && Z.ltb b two64 && Z.leb 0 nlo && Z.leb 0 vlo && Z.leb vlo hi && Z.leb hi vhi
&& Z.ltb (c * vhi) two64)%bool
then [KRange (EVar v) vlo hi] else []
| _, _, _ => []
end
| _, _ => []
end)).
{ destruct (scaled_var cA) as [[c v]|] eqn:HsA; [|constructor].
destruct cB as [b| | | | | | |]; try constructor.
destruct (xlo k (EVar v)) as [vlo|] eqn:Hvlo; [|constructor].
destruct (xhi k (EVar v)) as [vhi|] eqn:Hvhi; [|constructor].
destruct (xlo2 k nA) as [nlo|] eqn:Hnlo; [|constructor].
cbv zeta. match goal with |- Forall _ (if ?c then _ else _) => destruct c eqn:Ht; [|constructor] end.
repeat match type of Ht with (_ && _)%bool = true => apply andb_prop in Ht as [Ht ?X] end.
repeat match goal with H : Z.leb _ _ = true |- _ => apply Z.leb_le in H | H : Z.ltb _ _ = true |- _ => apply Z.ltb_lt in H end.
destruct (scaled_var_sound cA c v HsA) as [Hc HeA]. rewrite HeA in Hle.
pose proof (xlo_sound SEGS E M k (EVar v) vlo HK Hvlo) as L1.
pose proof (xhi_sound SEGS E M k (EVar v) vhi HK Hvhi) as L2.
pose proof (xlo2_sound E M k nA nlo HK Hnlo) as L3.
cbn [edenot] in L1, L2. cbn [edenot] in Hle. rewrite u_lit64 in Hle. unfold two64 in *.
rewrite (Z.mod_small b) in Hle by lia.
pose proof (u64_range (ev E v)) as Rv.
rewrite Z.mod_small in Hle by nia.
constructor; [|constructor]. cbn [kentry_ok edenot]. split; [exact L1|].
apply div_upper; [exact Hc|]. lia. }
destruct cA as [a| | | | | | |]; try exact CASE2.
destruct nA as [na| | | | | | |]; try exact CASE2.
destruct (scaled_var cB) as [[c v]|] eqn:HsB; [|exact CASE2].
clear CASE2.
destruct (xhi k (EVar v)) as [vhi|] eqn:Hvhi; [|constructor].
cbv zeta. match goal with |- Forall _ (if ?c then _ else _) => destruct c eqn:Ht; [|constructor] end.
repeat match type of Ht with (_ && _)%bool = true => apply andb_prop in Ht as [Ht ?X] end.
repeat match goal with H : Z.leb _ _ = true |- _ => apply Z.leb_le in H | H : Z.ltb _ _ = true |- _ => apply Z.ltb_lt in H end.
destruct (scaled_var_sound cB c v HsB) as [Hc HeB]. rewrite HeB in Hle.
pose proof (xhi_sound SEGS E M k (EVar v) vhi HK Hvhi) as L2. cbn [edenot] in L2.
cbn [edenot] in Hle. rewrite !u_lit64 in Hle. unfold two64 in *.
rewrite (Z.mod_small a), (Z.mod_small na) in Hle by lia.
pose proof (u64_range (ev E v)) as Rv.
rewrite Z.mod_small in Hle by nia.
constructor; [|constructor]. cbn [kentry_ok edenot]. split; [|exact L2].
apply div_lower; [exact Hc|]. lia.
Qed.
End SE.
#[using="Type"] Lemma casedisj_sound : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "R0'S6'Y@'Y=&R8y5'_2yR0%211%5241'@y8%611%311p061'QL'X4r4r9r3r2r1%6554321'H'B%12HH%@11&V7r:r8%332<1(4(Ar7r6%34Q2Q221%52;1%>3;71'L'Gr5%I57<1HF'Q3&VL%11?r;%311%H3531%9271%Q15?@9Q0N%71A%L3915%=231%?251p0A1p0Q11pl4Q91pRFQ;1pTNQA1pR<QH1pi8QK1pi6QL1pgLQL1pgJQM1phNQO1").
Proof.
intros cs b1 b2 csa csb E R FULL model HC H. unfold node_casedisj in H.
pose proof (co_know _ _ _ _ _ HC) as HK.
destruct (find_disj (kn cs) b1 b2) as [[[[[[c1 o1] n1] c2] o2] n2]|] eqn:Hf; [|discriminate].
destruct (flat_x (kn cs) c1 o1 n1) eqn:F1; [|discriminate].
destruct (flat_x (kn cs) c2 o2 n2) eqn:F2; [|cbn in H; discriminate].
destruct (disj_side_fact (kn cs) c1 o1 n1 c2 o2) as [K1|] eqn:D1; [|discriminate].
destruct (disj_side_fact (kn cs) c2 o2 n2 c1 o1) as [K2|] eqn:D2; [|discriminate].
injection H as <- <-.
pose proof (flat_x_sound E _ (kn cs) c1 o1 n1 HK F1) as (A1 & A2 & A3).
pose proof (flat_x_sound E _ (kn cs) c2 o2 n2 HK F2) as (B1 & B2 & B3).
unfold elenZ in *.
destruct (find_disj_sound E _ (kn cs) b1 b2 c1 o1 n1 c2 o2 n2 HK Hf) as [Hd|Hd].
- left. split; [|reflexivity]. unfold add_kn. apply cs_ok_set_kn; [exact HC|]. constructor.
+ eapply disj_side_fact_sound; [exact HK | exact D1 | lia | unfold elenZ in *; lia | exact Hd].
+ apply Forall_app. split; [|exact HK]. eapply disj_var_fact_sound; [exact HK | exact Hd].
- right. split; [|reflexivity]. unfold add_kn. apply cs_ok_set_kn; [exact HC|]. constructor.
+ eapply disj_side_fact_sound; [exact HK | exact D2 | lia | unfold elenZ in *; lia | exact Hd].
+ apply Forall_app. split; [|exact HK]. eapply disj_var_fact_sound; [exact HK | exact Hd].
Qed.
#[using="SHADOW_ok"] Lemma shadow_of_val : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "RB'Y='_2yR0%211'@y8%511%311p051'<'YE%211'Y@'Q3&Z6vZJr8r7r6%544321'H'B%12:9%221;&W:v0r5%342:91(Ar4r3%34CB21r2%54;E21%>3;71'7&T7%14E;87(D%C3421'G&Z4r;(Y8%12JB%4231&[5&[1&[2&_3&Y<%129Q3%32QB1+8%6221&W;%11O%:231&[9+2+R0%3221%@251%Q;3QBB1&Z3%12GQ4%@2HQA%B2R11%D21?%QA3QH41%N271p0Q01p0Q61p0QF1pmJQN1pmHQN1pmBR01pl:R11pgFR21pk0R41pTDR81pR<RA1").
Proof.
intros E M k b n sb sk sn HK Hs Hf. unfold shadow_of in Hs.
destruct (split_lit (eadd (mkSrl k b 3) (ELit (shadow_off A)))) as [sb' sk'] eqn:Hsp. injection Hs as E1 E2 E3. subst sb' sk'. rewrite <- E3 in *.
pose proof (flat_x_sound E _ k sb sk (mkSrl k n 3) HK Hf) as (F1 & F2 & F3).
pose proof (split_lit_denot E _ sb sk Hsp) as Hd.
assert (S3 : forall x, bv_unsigned (edenot E (mkSrl k x 3)) = bv_unsigned (edenot E x) / 8).
{ intros x. rewrite (mkSrl_denot SEGS E _ k x 3 (Z_to_bv 64 3) HK) by reflexivity.
rewrite u_srl64. rewrite u64_lit by lia. reflexivity. }
split.
- unfold eadd in Hd. rewrite mkAlu_denot in Hd. apply (f_equal bv_unsigned) in Hd.
rewrite u_add64, S3 in Hd. cbn [edenot] in Hd. rewrite (u64_lit (shadow_off A)) in Hd by (pose proof SHADOW_ok as SO; unfold shadow_ok in SO; lia).
rewrite Z_to_bv_unsigned in Hd. unfold bv_wrap, bv_modulus in Hd. change (2 ^ Z.of_N 64) with (2 ^ 64) in Hd.
unfold estart; cbn [a_base a_off].
pose proof (u64_range (edenot E (mkSrl k n 3))). unfold elenZ, estart in *; cbn [a_base a_off] in *.
unfold two64 in *. rewrite (Z.mod_small (bv_unsigned (edenot E sb) + sk)) in Hd by lia.
rewrite <- Hd. reflexivity.
- unfold elenZ. apply S3.
Qed.
#[using="SHADOW_ok"] Lemma shdisj_sound : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "QI'S6'Y@'Y=&R8y5'_2yR0%211%5241'@y8%611%311p061'QL'X4r4r:r3r2r1%6554321'H%>1G&VFv0r;r9r8r7%6654=321(4r6%22Q11%<3;41'Gr5%F5581EC'Q3&VL%11;r<%311%E3531%9271p0;1p0I1pl4Q11pRFQ31pTNQ91pR<Q@1pi0QC1pl>QC1pgLQD1pl<QE1pgJQF1phNQH1").
Proof.
intros cs b1 n1 b2 n2 cs' E R FULL model HC H. rewrite node_shdisj_eq in H. unfold node_shdisj_ref in H.
pose proof (co_know _ _ _ _ _ HC) as HK.
destruct (split_lit b1) as [c1 o1] eqn:S1. destruct (split_lit b2) as [c2 o2] eqn:S2.
destruct (shadow_of A (kn cs) b1 n1) as [[sb1 sk1] sn1] eqn:H1. destruct (shadow_of A (kn cs) b2 n2) as [[sb2 sk2] sn2] eqn:H2.
match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end. injection H as <-.
apply andb_prop in Hc as [Hc Hap]. apply andb_prop in Hc as [Hc Hhi]. apply andb_prop in Hc as [Hc Fs2]. apply andb_prop in Hc as [Hc Fs1].
apply andb_prop in Hc as [Hc F2]. apply andb_prop in Hc as [Hc F1].
apply andb_prop in Hc as [Hc Ln2]. apply andb_prop in Hc as [Hc Lb2]. apply andb_prop in Hc as [Lb1 Ln1].
apply Z.leb_le in Lb1. apply Z.leb_le in Ln1. apply Z.leb_le in Lb2. apply Z.leb_le in Ln2.
split; [|reflexivity]. unfold add_kn. apply cs_ok_set_kn; [exact HC|]. constructor; [|exact HK].
destruct (xhi (kn cs) b1) as [h1|] eqn:Xh1; [|discriminate]. destruct (xhi (kn cs) n1) as [m1|] eqn:Xm1; [|discriminate].
destruct (xhi (kn cs) b2) as [h2|] eqn:Xh2; [|discriminate]. destruct (xhi (kn cs) n2) as [m2|] eqn:Xm2; [|discriminate].
apply andb_prop in Hhi as [Y1 Y2]. apply Z.leb_le in Y1. apply Z.leb_le in Y2.
pose proof (xhi_sound SEGS E _ (kn cs) b1 h1 HK Xh1) as B1. pose proof (xhi_sound SEGS E _ (kn cs) n1 m1 HK Xm1) as M1.
pose proof (xhi_sound SEGS E _ (kn cs) b2 h2 HK Xh2) as B2. pose proof (xhi_sound SEGS E _ (kn cs) n2 m2 HK Xm2) as M2.
pose proof (flat_x_sound E _ (kn cs) c1 o1 n1 HK F1) as (A1 & A2 & A3).
pose proof (flat_x_sound E _ (kn cs) c2 o2 n2 HK F2) as (C1 & C2 & C3).
pose proof (u64_range (edenot E n1)) as Rn1. pose proof (u64_range (edenot E n2)) as Rn2.
pose proof (u_of_split E b1 c1 o1 S1 ltac:(lia)) as U1. pose proof (u_of_split E b2 c2 o2 S2 ltac:(lia)) as U2.
pose proof (ranges_apart_x_sound SEGS E _ (kn cs) c1 o1 n1 c2 o2 n2 HK Hap) as AP0.
destruct (shadow_of_val E _ (kn cs) b1 n1 sb1 sk1 sn1 HK H1 Fs1) as [V1 L1].
destruct (shadow_of_val E _ (kn cs) b2 n2 sb2 sk2 sn2 HK H2 Fs2) as [V2 L2].
pose proof SHADOW_ok as SO; unfold shadow_ok in SO.
cbn [kentry_ok]. rewrite V1, V2, L1, L2.
destruct (ealign_sound SEGS E _ (kn cs) b1 HK) as [_ D1]. destruct (ealign_sound SEGS E _ (kn cs) n1 HK) as [_ D2].
destruct (ealign_sound SEGS E _ (kn cs) b2 HK) as [_ D3]. destruct (ealign_sound SEGS E _ (kn cs) n2 HK) as [_ D4].
assert (P8 : forall e, 3 <= ealign (kn cs) e -> (2 ^ ealign (kn cs) e | bv_unsigned (edenot E e)) -> (8 | bv_unsigned (edenot E e))).
{ intros e He Hd. eapply Z.divide_trans; [|exact Hd]. change 8 with (2 ^ 3). apply pow2_divide_le. lia. }
pose proof (P8 _ Lb1 D1) as [q1 Q1]. pose proof (P8 _ Ln1 D2) as [q2 Q2]. pose proof (P8 _ Lb2 D3) as [q3 Q3]. pose proof (P8 _ Ln2 D4) as [q4 Q4].
unfold elenZ in AP0. rewrite <- U1, <- U2 in AP0.
pose proof (u64_range (edenot E b1)) as Rb1. pose proof (u64_range (edenot E b2)) as Rb2.
generalize dependent AP0. rewrite Q1, Q2, Q3, Q4. rewrite Q1 in Rb1, B1. rewrite Q2 in Rn1, M1. rewrite Q3 in Rb2, B2. rewrite Q4 in Rn2, M2.
rewrite !Z.div_mul by lia. intros AP0.
rewrite (Z.mod_small (q1 + shadow_off A)) by lia. rewrite (Z.mod_small (q3 + shadow_off A)) by lia.
clear - AP0 Rb1 Rb2 Rn1 Rn2 SO. lia.
Qed.
Section SE.
Local Abbreviation SEC_T_kdisj_shadow_twin_ok := (ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "Q3'Y='_2yR0%211'@y8%511%311p051'<'YE%211&Z6vZJr5r4r3%544321&Z5r6%247164'Q0r7%53:17&TMv0%231<;%63A41p081p0<1pTFF1pS8E1pk0E1pTDI1pR<Q21")) (only parsing).
Variable E : ltac:(sec_ty2 constr:(SEC_T_kdisj_shadow_twin_ok) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_kdisj_shadow_twin_ok) 1%nat 0%nat).
Variable k : ltac:(sec_ty2 constr:(SEC_T_kdisj_shadow_twin_ok) 2%nat 0%nat).
Lemma kdisj_shadow_twin_ok : ltac:(sec_stmt2 constr:(SEC_T_kdisj_shadow_twin_ok) 3%nat 0%nat).
Proof using SHADOW_ok E M k.
intros K M' HK HKK.
unfold kdisj_shadow_twin.
destruct K as [| | | | | | |[b1 o1z] n1 [b2 o2z] n2| |]; try constructor.
destruct o1z; try constructor. destruct o2z; try constructor.
destruct (split_lit b1) as [c1 o1] eqn:S1. destruct (split_lit b2) as [c2 o2] eqn:S2.
destruct (shadow_of A k b1 n1) as [[sb1 sk1] sn1] eqn:H1. destruct (shadow_of A k b2 n2) as [[sb2 sk2] sn2] eqn:H2.
match goal with |- Forall _ (if ?c then _ else _) => destruct c eqn:Hc; [|constructor] end.
apply andb_prop in Hc as [Hc Hhi]. apply andb_prop in Hc as [Hc Fs2]. apply andb_prop in Hc as [Hc Fs1].
apply andb_prop in Hc as [Hc F2]. apply andb_prop in Hc as [Hc F1].
apply andb_prop in Hc as [Hc Ln2]. apply andb_prop in Hc as [Hc Lb2]. apply andb_prop in Hc as [Lb1 Ln1].
apply Z.leb_le in Lb1. apply Z.leb_le in Ln1. apply Z.leb_le in Lb2. apply Z.leb_le in Ln2.
destruct (xhi k (eadd b1 n1)) as [e1|] eqn:Xe1; [|discriminate]. destruct (xhi k (eadd b2 n2)) as [e2|] eqn:Xe2; [|discriminate].
destruct (xhi k b1) as [h1|] eqn:Xh1; [|discriminate]. destruct (xhi k n1) as [m1|] eqn:Xm1; [|discriminate].
destruct (xhi k b2) as [h2|] eqn:Xh2; [|discriminate]. destruct (xhi k n2) as [m2|] eqn:Xm2; [|discriminate].
apply andb_prop in Hhi as [Hhi W2]. apply andb_prop in Hhi as [Hhi W1]. apply andb_prop in Hhi as [Y1 Y2].
apply Z.leb_le in Y1. apply Z.leb_le in Y2. apply Z.ltb_lt in W1. apply Z.ltb_lt in W2. unfold two64 in W1, W2.
pose proof (xhi_sound SEGS E _ k (eadd b1 n1) e1 HK Xe1) as E1. pose proof (xhi_sound SEGS E _ k (eadd b2 n2) e2 HK Xe2) as E2.
pose proof (xhi_sound SEGS E _ k b1 h1 HK Xh1) as B1. pose proof (xhi_sound SEGS E _ k n1 m1 HK Xm1) as M1.
pose proof (xhi_sound SEGS E _ k b2 h2 HK Xh2) as B2. pose proof (xhi_sound SEGS E _ k n2 m2 HK Xm2) as M2.
unfold eadd in E1, E2. rewrite mkAlu_denot in E1, E2. cbn [alu64 alu] in E1, E2. rewrite bv_add_unsigned in E1, E2.
unfold bv_wrap in E1, E2. change (bv_modulus 64) with (2 ^ 64) in E1, E2.
pose proof (u64_range (edenot E b1)) as Rb1. pose proof (u64_range (edenot E b2)) as Rb2.
pose proof (u64_range (edenot E n1)) as Rn1. pose proof (u64_range (edenot E n2)) as Rn2.
rewrite Z.mod_small in E1 by lia. rewrite Z.mod_small in E2 by lia.
pose proof (flat_x_sound E _ k c1 o1 n1 HK F1) as (A1 & A2 & A3).
pose proof (flat_x_sound E _ k c2 o2 n2 HK F2) as (C1 & C2 & C3).
pose proof (u_of_split E b1 c1 o1 S1 ltac:(lia)) as U1. pose proof (u_of_split E b2 c2 o2 S2 ltac:(lia)) as U2.
cbn [kentry_ok] in HKK. unfold estart, elenZ in HKK. cbn [a_base a_off] in HKK. rewrite !Z.add_0_r in HKK.
destruct (shadow_of_val E _ k b1 n1 sb1 sk1 sn1 HK H1 Fs1) as [V1 L1].
destruct (shadow_of_val E _ k b2 n2 sb2 sk2 sn2 HK H2 Fs2) as [V2 L2].
pose proof SHADOW_ok as SO; unfold shadow_ok in SO.
constructor; [|constructor]. cbn [kentry_ok]. rewrite V1, V2, L1, L2.
destruct (ealign_sound SEGS E _ k b1 HK) as [_ D1]. destruct (ealign_sound SEGS E _ k n1 HK) as [_ D2].
destruct (ealign_sound SEGS E _ k b2 HK) as [_ D3]. destruct (ealign_sound SEGS E _ k n2 HK) as [_ D4].
assert (P8 : forall e, 3 <= ealign k e -> (2 ^ ealign k e | bv_unsigned (edenot E e)) -> (8 | bv_unsigned (edenot E e))).
{ intros e He Hd. eapply Z.divide_trans; [|exact Hd]. change 8 with (2 ^ 3). apply pow2_divide_le. lia. }
pose proof (P8 _ Lb1 D1) as [q1 Q1]. pose proof (P8 _ Ln1 D2) as [q2 Q2]. pose proof (P8 _ Lb2 D3) as [q3 Q3]. pose proof (P8 _ Ln2 D4) as [q4 Q4].
generalize dependent HKK. rewrite Q1, Q2, Q3, Q4. rewrite Q1 in Rb1, B1, E1. rewrite Q2 in Rn1, M1, E1. rewrite Q3 in Rb2, B2, E2. rewrite Q4 in Rn2, M2, E2.
rewrite !Z.div_mul by lia. intros HKK.
rewrite (Z.mod_small (q1 + shadow_off A)) by lia. rewrite (Z.mod_small (q3 + shadow_off A)) by lia.
clear - HKK Rb1 Rb2 Rn1 Rn2 SO. lia.
Qed.
End SE.
#[using="SHADOW_ok"] Lemma kdisj_shadow_twins_ok : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "Q6'Y='_2yR0%211'@y8%511%311p051'<'YE%211&Z6vZJr5r4r3%544321'Q0&Z5r6%23817%43<16r7%53;18&ZN&TMv0%221>%44CC1>%<3D61p091p0?1pTFI1pk<G1pk0H1pTDL1pR<Q51").
Proof.
intros E M k l M' HK Hl. apply Forall_flat_map. eapply Forall_impl; [|exact Hl]. intros K HKK. eapply kdisj_shadow_twin_ok; eassumption.
Qed.
#[using="Type"] Lemma expr_vars_lt_mono : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "D'='Y@'H'7&T3r3r1%3221(D%73621'Nr4%2217%9228%<3;16p031p071pi@@1pgHB1pgFC1").
Proof.
intros b b' e H Hle. induction e; cbn [APK.expr_vars_lt] in *; try reflexivity;
try (apply andb_prop in H as [H1 H2]; rewrite (IHe1 H1), (IHe2 H2); reflexivity); try (apply IHe; exact H).
apply Nat.ltb_lt in H. apply Nat.ltb_lt. lia.
Qed.
#[using="Type"] Lemma sr_vars_lt_mono : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "F'='<'Y@%211'H'7&WBr3r1%3221(D%73621'Nr4%2217%9228%<3;16p031p071pmL@1pgHD1pgFE1").
Proof.
intros b b' sr H Hle. induction sr; cbn [APK.sr_vars_lt] in *; [reflexivity|].
apply andb_prop in H as [H1 H2]. rewrite (expr_vars_lt_mono _ _ _ H1 Hle), (IHsr H2). reflexivity.
Qed.
#[using="Type"] Lemma sr_vars_lt_upd : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "L'='<'Y@%211'H'7&WBr4r3%3221(D%73621&T3r5r2%3221%<3;16r6&YO%136<;%>231%A3@1;p061p0<1pi@F1pl:I1pmLG1pgFK1").
Proof.
intros b sr n e. revert sr. induction n as [|n IH]; intros sr Hsr He.
- destruct sr; cbn [sr_upd APK.sr_vars_lt]; cbn [APK.sr_vars_lt] in Hsr; rewrite He; [reflexivity|].
apply andb_prop in Hsr as [_ H2]. rewrite H2. reflexivity.
- destruct sr; cbn [sr_upd APK.sr_vars_lt]; cbn [APK.sr_vars_lt] in Hsr.
+ rewrite IH by (reflexivity || exact He). reflexivity.
+ apply andb_prop in Hsr as [H1 H2]. rewrite H1, (IH _ H2 He). reflexivity.
Qed.
Fixpoint ext_list (E : env) (nx : nat) (vals : list word) : env :=
match vals with
| [] => E
| v :: rest => ext_list (ext1 E nx v) (Datatypes.S nx) rest
end.
#[using="Type"] Lemma ext_list_agree : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "A'Y='='<'_2yR0%211%411&Z9r2r3&X6r1%23341%63541po281plH>1pR<@1").
Proof.
intros E nx vals. revert E nx. induction vals as [|v rest IH]; intros E nx; cbn [ext_list].
- apply env_agree_refl.
- eapply env_agree_trans; [apply ext1_agree|]. eapply env_agree_le; [apply IH | lia].
Qed.
#[using="Type"] Lemma ext_list_at : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "Q2'Y='='<'_2yR0%211%411&Or1&;r2%2261%5241'H&Y?&X6r5r4r3%43321&M%124;%8231&Q2&_1z%22F1%44FA91%?3G61p0A1pjBM1po2I1plHO1pR<Q11").
Proof.
intros E nx vals. revert E nx. induction vals as [|v rest IH]; intros E nx i Hi; cbn [length] in Hi; [lia|].
cbn [ext_list]. destruct i as [|i].
- rewrite Nat.add_0_r. pose proof (ext_list_agree (ext1 E nx v) (Datatypes.S nx) rest) as [Hag _].
rewrite <- Hag by lia. cbn [nth]. apply ext1_at.
- replace (nx + Datatypes.S i)%nat with (Datatypes.S nx + i)%nat by lia. cbn [nth]. apply IH. lia.
Qed.
#[using="Type"] Lemma regs_ok_sr_fresh : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "QL'Y='<'Y@%211&R8y5'_2yR0%211%5241'=%:11&Z7r5r4r3%43321'H'7&WBr2%2218(D%63521'Q0'G&O(2r1%3221uQ0%5231%7231qm:G1%:3H1D&X6r8&Q1&Z?r7&_1&[7%11>%32Q61%6251qm:Q31%94Q4Q61Q1%<3;Q11&WA%13:Q4Q3r6%Q73421p0B1p0N1p0Q61plHQ=1pm>Q=1pTNQ@1pmLQG1pR<QK1").
Proof.
intros E sr R rs. revert E sr. induction rs as [|r rest IH]; intros E sr nx HR Hsr Hrs; cbn [sr_fresh map ext_list].
- exact HR.
- apply Forall_cons_iff in Hrs as [Hr Hrest].
apply IH.
+ apply regs_ok_respell.
* eapply regs_ok_agree'; [apply ext1_agree | exact Hsr | exact HR].
* exact Hr.
* cbn [edenot]. rewrite ext1_at.
pose proof (regs_ok_agree' nx E (ext1 E nx (getr R (Z_to_bv 5 (Z.of_nat r)))) sr R (ext1_agree _ _ _) Hsr HR) as HR'.
etransitivity; [exact (HR' (Z_to_bv 5 (Z.of_nat r)))|]. unfold sr_get.
assert (Hnz : bv_eqb (Z_to_bv 5 (Z.of_nat r)) 0%bv = false).
{ unfold bv_eqb. apply Z.eqb_neq. rewrite Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 5) with 32%Z. rewrite Z.mod_small by lia.
replace (bv_unsigned (0%bv : bv 5)) with 0%Z by reflexivity. lia. }
rewrite Hnz, ridx_lit by lia. reflexivity.
+ apply sr_vars_lt_upd; [eapply sr_vars_lt_mono; [exact Hsr | lia] |]. cbn [APK.expr_vars_lt]. apply Nat.ltb_lt. lia.
+ exact Hrest.
Qed.
#[using="e_sp0_init argH_agree SINV_agree"] Lemma havoc_sound : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "R0'Y='S6&R8y5'_2yR0%211%5241'@y8%611%311p061'QL'<'=%211'X4r7r6r5r4r3%6554321'H%A1H&V?v^<%231:6(4r2%22N1%83741'I'G&Z9r:r1%33;21&VIr9%211%73165%9251r8%L58H1KJ'Q3&VL%11K%219%J3421%A261%B291qR>QE1%E2QF1p0G1p0Q11pi0QH1pm>Q:1pl4Q>1pRFQ@1pTNQF1phNQM1pR<QO1").
Proof.
intros E cs R FULL model rs cs' HC H. unfold node_havoc in H.
destruct (fresh_ok nx0 cs && forallb (fun r => Nat.ltb 0 r && Nat.ltb r 32) rs)%bool eqn:Hc; [|discriminate].
injection H as <-. apply andb_prop in Hc as [Hf Hrs].
destruct (fresh_ok_parts cs Hf) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
set (E' := ext_list E (nxt cs) (map (fun r => getr R (Z_to_bv 5 (Z.of_nat r))) rs)).
assert (Hag : env_agree (nxt cs) E E') by apply ext_list_agree.
exists E'. split; [split; [eapply env_agree_le; [exact Hag | exact Fle] | exact Hag]|]. split; [|reflexivity].
pose proof (cs_ok_agree E E' cs R FULL model Hag Hf HC) as HC'.
destruct HC'; constructor; cbn [with_ss a_ss mk_ss s_regs s_log s_know kn a_maps a_totsz a_ylo a_eager a_vis a_abytes a_brk a_fd a_tidset a_hna a_hlz]; try assumption; [|reflexivity].
apply regs_ok_sr_fresh; [exact (co_regs _ _ _ _ _ HC) | exact Fsr |].
apply Forall_forall. intros r Hr. pose proof (proj1 (forallb_forall _ _) Hrs r Hr) as Hb.
apply andb_prop in Hb as [H1 H2]. apply Nat.ltb_lt in H1. apply Nat.ltb_lt in H2. lia.
Qed.
Fixpoint kn_bigexprs (K : nat) (k : list kentry) : list expr :=
match k with
| [] => []
| KWord a w v :: r => if bigb K v then v :: kn_bigexprs K r else kn_bigexprs K r
| _ :: r => kn_bigexprs K r
end.
#[using="Type"] Lemma kentry_vars_lt_mono : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "D'='YE'H'7&U2r3r1%3221(D%73621'Nr4%2217%9228%<3;16p031p071pS8@1pgHB1pgFC1").
Proof.
intros b b' K H Hle.
assert (E1 : forall e, APK.expr_vars_lt b e = true -> APK.expr_vars_lt b' e = true) by (intros; eapply expr_vars_lt_mono; eassumption).
assert (A1 : forall a, APK.saddr_vars_lt b a = true -> APK.saddr_vars_lt b' a = true) by (intros [? ?]; unfold APK.saddr_vars_lt; apply E1).
destruct K; cbn [APK.kentry_vars_lt] in *;
repeat match type of H with (_ && _)%bool = true => apply andb_prop in H as [H ?X] end;
repeat match goal with
| Y : APK.expr_vars_lt b ?e = true |- _ => rewrite (E1 e Y); clear Y
| Y : APK.saddr_vars_lt b ?a = true |- _ => rewrite (A1 a Y); clear Y
end; reflexivity.
Qed.
#[using="Type"] Lemma kn_vars_lt_mono' : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "F'='<'YE%211'H'7&U=r3r1%3221(D%73621'Nr4%2217%9228%<3;16p031p071pk0@1pgHD1pgFE1").
Proof.
intros b b' k H Hle. induction k as [|K k IH]; [reflexivity|]. cbn [APK.kn_vars_lt] in *. apply andb_prop in H as [H1 H2].
rewrite (kentry_vars_lt_mono b b' K H1 Hle), (IH H2). reflexivity.
Qed.
#[using="Type"] Lemma kn_bigsubst_len : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "E'='<'YE%211'H&C&U8r3r2r1%43321%638;1&;'Y@&XB%1287%4231%=3A61plHB1pk0@1pS8D1").
Proof.
intros K k. induction k as [|x r IH]; intros nx; [reflexivity|].
cbn [kn_bigsubst kn_bigexprs]. destruct x as [a w v| | | | | | | | |]; try (specialize (IH nx); destruct (kn_bigsubst K r nx); cbn in *; exact IH).
destruct (bigb K v).
- specialize (IH (Datatypes.S nx)). destruct (kn_bigsubst K r (Datatypes.S nx)). cbn in *. rewrite IH. reflexivity.
- specialize (IH nx). destruct (kn_bigsubst K r nx). cbn in *. exact IH.
Qed.
Section SE.
Local Abbreviation SEC_T_kn_bigsubst_sound := (ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "R1'='<'YE%211'Y='_2yR0%211'@y8%511%311p051&Z6vZJr2r1r4%544321'H'7&U=r5%2261(D%63521&O&;'Y@&XBr8r7%3221%6251%82B1&Y?r6&M%127G%4231&Y<&Q2r9%>21=(Y2z%211%64CQ041%82<1%N3Q::1p0@1pjBQC1&:&U8%13HGB%33QDQG1%Q;4Q:Q2Q71p061p0Q11p0Q91pTDQ@1pRBQI1plHQN1pk0QL1pS8R01")) (only parsing).
Variable K : ltac:(sec_ty2 constr:(SEC_T_kn_bigsubst_sound) 0%nat 0%nat).
Lemma kn_bigsubst_sound : ltac:(sec_stmt2 constr:(SEC_T_kn_bigsubst_sound) 1%nat 0%nat).
Proof using Type K.
intros k.
induction k as [|x r IH]; intros nx E2 M HK Hv Hvals; [constructor|].
inversion HK as [|x' r' Hx Hr]; subst. cbn [APK.kn_vars_lt] in Hv. apply andb_prop in Hv as [Hvx Hvr].
cbn [kn_bigsubst]. cbn [kn_bigexprs] in Hvals.
assert (DFLT : (forall i, (i < length (kn_bigexprs K r))%nat -> ev E2 (nx + i) = edenot E2 (nth i (kn_bigexprs K r) (ELit 0))) ->
know_ok SEGS E2 M (fst (let '(r', c) := kn_bigsubst K r nx in (x :: r', c)))).
{ intros Hvals'. pose proof (IH nx E2 M Hr Hvr Hvals') as IH'. destruct (kn_bigsubst K r nx) as [r' c]. cbn [fst] in *. constructor; [exact Hx | apply IH']. }
destruct x as [a w v| | | | | | | | |]; try (apply DFLT; exact Hvals).
destruct (bigb K v) eqn:Hb; [|apply DFLT; exact Hvals]. clear DFLT.
pose proof (IH (Datatypes.S nx) E2 M Hr ltac:(eapply kn_vars_lt_mono'; [exact Hvr | lia])) as IH'.
destruct (kn_bigsubst K r (Datatypes.S nx)) as [r' c] eqn:Hs. cbn [fst]. constructor.
- cbn [kentry_ok] in Hx |- *. destruct Hx as (H1 & H2 & H3). split; [exact H1|]. split; [exact H2|].
rewrite H3. f_equal. f_equal. cbn [edenot]. symmetry. replace nx with (nx + 0)%nat by lia. rewrite (Hvals 0%nat ltac:(cbn; lia)). reflexivity.
- apply IH'. intros i Hi. replace (Datatypes.S nx + i)%nat with (nx + Datatypes.S i)%nat by lia. rewrite (Hvals (Datatypes.S i) ltac:(cbn; lia)). reflexivity.
Qed.
End SE.
#[using="Type"] Lemma node_havoc_nxt : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "Q4'S6'<'=%211'H'@%116&V?v^<r3r2%43321(4r1%22>1%;3941'G&VI%118&Mr4%411&;%12E>%5231%E3G71'Q3&VL%11B%219%J3421%?261p0A1pi2Q11pm>O1phNQ31").
Proof.
intros cs rs cs1 H. unfold node_havoc in H.
destruct (fresh_ok nx0 cs && forallb (fun r : nat => Nat.ltb 0 r && Nat.ltb r 32) rs)%bool; [|discriminate].
injection H as <-. split; reflexivity.
Qed.
Section SE.
Local Abbreviation SEC_T_havocbig_sound := (ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "QN'Y='S6&R8y5'_2yR0%211%5241'@y8%611%311p061'QL'='X4r7r6r5r4r3%6554321'H%?1F&V@v^<%231:6(4r2%22L1%83741'I'G&Z9r:r1%33;21&VIr9%211%73165%9251r8%L58H1KJ'Q3&VL%11K%219%J3421%A261%B291qR>QC1%E2QD1p0G1p0Q11pi0QF1pS8Q:1pl4Q<1pRFQ>1pTNQD1phNQK1pR<QM1")) (only parsing).
Variable E : ltac:(sec_ty2 constr:(SEC_T_havocbig_sound) 0%nat 0%nat).
Variable cs : ltac:(sec_ty2 constr:(SEC_T_havocbig_sound) 1%nat 0%nat).
Variable R : ltac:(sec_ty2 constr:(SEC_T_havocbig_sound) 2%nat 0%nat).
Variable FULL : ltac:(sec_ty2 constr:(SEC_T_havocbig_sound) 3%nat 0%nat).
Variable model : ltac:(sec_ty2 constr:(SEC_T_havocbig_sound) 4%nat 0%nat).
Variable K : ltac:(sec_ty2 constr:(SEC_T_havocbig_sound) 5%nat 0%nat).
Variable cs' : ltac:(sec_ty2 constr:(SEC_T_havocbig_sound) 6%nat 0%nat).
Lemma havocbig_sound : ltac:(sec_stmt2 constr:(SEC_T_havocbig_sound) 7%nat 0%nat).
Proof using e_sp0_init argH_agree SINV_agree E cs R FULL model K cs'.
intros HC H.
unfold node_havocbig in H.
destruct (node_havoc nx0 cs _) as [cs1|] eqn:Hh; [|discriminate].
destruct (fresh_ok nx0 cs1) eqn:Hf1; [|discriminate].
destruct (kn_bigsubst K (kn cs1) (nxt cs1)) as [k' c] eqn:Hs. injection H as <-.
destruct (havoc_sound E cs R FULL model _ cs1 HC Hh) as (E1 & [Hag0 Hag1] & HC1 & Hpc1).
destruct (fresh_ok_parts cs1 Hf1) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
set (vals := map (edenot E1) (kn_bigexprs K (kn cs1))).
set (E2 := ext_list E1 (nxt cs1) vals).
assert (Hag2 : env_agree (nxt cs1) E1 E2) by apply ext_list_agree.
assert (Hnx : (nxt cs <= nxt cs1)%nat).
{ destruct (node_havoc_nxt cs _ cs1 Hh) as [-> _]. lia. }
exists E2. split; [|split; [|rewrite <- Hpc1; reflexivity]].
{ split; (eapply env_agree_trans; [|eapply env_agree_le; [exact Hag2 | lia]]); assumption. }
pose proof (cs_ok_agree E1 E2 cs1 R FULL model Hag2 Hf1 HC1) as HC2.
replace (with_ss cs1 (mk_ss (pc cs1) (s_regs (a_ss cs1)) k' (nxt cs1 + c))) with (set_kn (bump cs1 c) k') by reflexivity.
apply cs_ok_set_kn.
- destruct HC2; constructor; cbn [bump with_ss a_ss mk_ss s_regs s_log s_know kn a_maps a_totsz a_ylo a_eager a_vis a_abytes a_brk a_fd a_tidset a_hna a_hlz];
try assumption; reflexivity.
- replace k' with (fst (kn_bigsubst K (kn cs1) (nxt cs1))) by (rewrite Hs; reflexivity).
unfold Mr. change (hid E2 (bump cs1 c) model) with (hid E2 cs1 model).
apply kn_bigsubst_sound; [exact (co_know _ _ _ _ _ HC2) | rewrite kn_vars_lt_eq; rewrite <- kn_vars_lt_eq; exact Fkn |].
intros i Hi. unfold E2. rewrite ext_list_at by (unfold vals; rewrite length_map; exact Hi).
unfold vals. change (Z_to_bv 64 0) with (edenot E1 (ELit 0)). rewrite map_nth.
eapply (edenot_agree' (nxt cs1)); [apply ext_list_agree|].
clear - Fkn Hi. revert i Hi. generalize (kn cs1) Fkn. intros k Hk.
induction k as [|x r IH]; intros i Hi; [cbn in Hi; lia|].
cbn [APK.kn_vars_lt] in Hk. apply andb_prop in Hk as [Hx Hr]. cbn [kn_bigexprs] in Hi |- *.
destruct x as [a w v| | | | | | | | |]; try (apply IH; assumption).
destruct (bigb K v); [|apply IH; assumption].
destruct i as [|i]; cbn [nth]; [cbn [APK.kentry_vars_lt] in Hx; apply andb_prop in Hx as [_ Hx]; exact Hx | apply IH; [exact Hr | cbn [length] in Hi; lia]].
Qed.
End SE.
Definition upd (E : env) (J : nat) (w : word) : env := Env (fun n => if Nat.eqb n J then w else ev E n) (eb E).
#[using="Type"] Lemma esubst_denot : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "H'Y='='Y@'H'_2yR0%211&Y<r4&T1r3r2r1%43321%7261&XI%9285%23971%;216%@3=51po>B1pi@C1pS6E1pR<G1").
Proof.
intros E J e x. induction x as [z|n|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|sx lo n a IHa|sx k i n];
cbn [esubst edenot]; try reflexivity.
- cbn [upd ev]. destruct (Nat.eqb n J); reflexivity.
- rewrite mkAlu_denot, IHa, IHb. reflexivity.
- rewrite mkAluw_denot, IHa, IHb. reflexivity.
- rewrite mkMd_denot, IHa, IHb. reflexivity.
- rewrite mkMdw_denot, IHa, IHb. reflexivity.
- rewrite IHa. reflexivity.
Qed.
#[using="Type"] Lemma upd_agree : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "?'Y='='_2yR0%211&Z9r2r3&XIr1%23341%63541po481pS6<1pR<>1").
Proof. intros E J w. split; [|reflexivity]. intros n Hn. cbn [upd ev]. destruct (Nat.eqb_spec n J); [lia|reflexivity]. Qed.
#[using="Type"] Lemma upd_at : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "A'Y='='_2yR0%211'H&Y?&XIr3r2r1%43321%6213%83913po4:1pS6>1pR<@1").
Proof. intros. cbn [upd ev]. rewrite Nat.eqb_refl. reflexivity. Qed.
#[using="Type"] Lemma upd_same : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "<'Y='='H&XIr2r1&Y?%1232%53431%73915pS691pR<;1").
Proof. intros [f g] J. unfold upd. cbn [ev eb]. f_equal. apply functional_extensionality. intros n. destruct (Nat.eqb_spec n J); [subst; reflexivity|reflexivity]. Qed.
#[using="Type"] Lemma upd_upd : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "C'Y='='_2yR0%211'H&XIr4r3r2%43321r1%63241%73652%93>21po6;1po4<1pS6@1pR<B1").
Proof. intros [f g] J w w'. unfold upd. cbn [ev eb]. f_equal. apply functional_extensionality. intros n. destruct (Nat.eqb n J); reflexivity. Qed.
#[using="Type"] Lemma estart_asubst : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "H'Y='='Y@'YL'H'Q3&Z4r4&S>r3r2r1%43321%7261&XI&Y<%1296%33:81%<217%?3>61pg@A1pi@C1pS6E1pR<G1").
Proof. intros E J e [b o]. unfold asubst, estart. cbn [a_base a_off]. rewrite esubst_denot. reflexivity. Qed.
#[using="Type"] Lemma adenot_asubst : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "J'Y='='Y@'YL'H'_2yR0%211&Y9r4&S>r3r2r1%43321%7261&XI&Y<%1296%33:81%<217%A3>61pg@C1pi@E1pS6G1pR<I1").
Proof. intros E J e [b o]. unfold asubst, adenot. cbn [a_base a_off]. rewrite esubst_denot. reflexivity. Qed.
Section SE.
Local Abbreviation SEC_T_kentry_ok_ksubst := (ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "Q2'Y='='Y@'_2yR0%211'@y8%511%311p051'YE&J&Z5vZJr5r2&U?r4r3r1%43321%948761&XI&Y<%12:6%33;81%>4=1;7%@261pS8B1pTDD1pi@M1pS6O1pR<Q11")) (only parsing).
Variable E : ltac:(sec_ty2 constr:(SEC_T_kentry_ok_ksubst) 0%nat 0%nat).
Variable J : ltac:(sec_ty2 constr:(SEC_T_kentry_ok_ksubst) 1%nat 0%nat).
Variable e : ltac:(sec_ty2 constr:(SEC_T_kentry_ok_ksubst) 2%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_kentry_ok_ksubst) 3%nat 0%nat).
Lemma kentry_ok_ksubst : ltac:(sec_stmt2 constr:(SEC_T_kentry_ok_ksubst) 4%nat 0%nat).
Proof using Type E J e M.
intros K.
set (E' := upd E J (edenot E e)).
destruct K as [a w v|a n|a n k|lo hi|x m|x lo hi|a n|a1 n1 a2 n2|a n c|a n]; cbn [ksubst kentry_ok];
unfold flat, elenZ; rewrite ?estart_asubst, ?adenot_asubst, ?esubst_denot; fold E'; tauto.
Qed.
End SE.
#[using="Type"] Lemma know_ok_ksubst : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "Q6'Y='='Y@'_2yR0%211'@y8%511%311p051'<'YE%211&J&Z6vZJr5r2&Q1&U?r4r3%3221r1%64==21%;4:981&XI&Y<%12<7%33=91%@4?1=7%B261pk0D1pTDH1pi@Q11pS6Q31pR<Q51").
Proof.
intros E J e M k. unfold know_ok. induction k as [|K k IH]; [split; intros; constructor|].
cbn [map]. split; intros H; inversion H; subst; constructor; try (apply IH; assumption);
apply (kentry_ok_ksubst E J e M K); assumption.
Qed.
#[using="Type"] Lemma inst_allowA : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "L'Y='='Y@'S6'H'<'B'Q3%2211%411&X2r4&TIr1r3r2%43321%7261&XI&Y<%1295%33:71%<219%C3>61pjFE1pi@G1pS6I1pR<K1").
Proof.
intros E J e inv. unfold allowA, inst. cbn [a_vis a_ghost]. rewrite <- map_app, flat_map_concat_map, flat_map_concat_map, map_map.
f_equal. apply map_ext. intros [b n]. unfold allow1, psubst, sh_lo, sh_hi, uE. cbn [fst snd]. rewrite !esubst_denot. reflexivity.
Qed.
#[using="Type"] Lemma existsb_map' : forall {X Y} (f : Y -> bool) (g : X -> Y) l, existsb f (map g l) = existsb (fun x => f (g x)) l.
Proof. intros X Y f g l. induction l as [|x l IH]; [reflexivity|]. cbn. rewrite IH. reflexivity. Qed.
#[using="Type"] Lemma inst_in_allow : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "J'Y='='Y@'S6'H'Q3'7poF21&X=r4&TIr1r3r2%43321%7261&XI&Y<%1295%33:71%<219%A3>61pjFC1pi@E1pS6G1pR<I1").
Proof.
intros E J e inv. apply functional_extensionality. intros z. unfold in_allow, in_vis, in_sh, inst. cbn [a_vis].
rewrite !existsb_map'. f_equal; f_equal; apply functional_extensionality; intros [b n];
unfold psubst, sh_lo, sh_hi, uE; cbn [fst snd]; rewrite !esubst_denot; reflexivity.
Qed.
#[using="Type"] Lemma inst_in_ghost : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "J'Y='='Y@'S6'H'Q3'7poF21&X>r4&TIr1r3r2%43321%7261&XI&Y<%1295%33:71%<219%A3>61pjFC1pi@E1pS6G1pR<I1").
Proof.
intros E J e inv. apply functional_extensionality. intros z. unfold in_ghost, inst. cbn [a_ghost].
induction (a_ghost inv) as [|[b n] l IH]; [reflexivity|]. cbn [map existsb fst snd psubst].
unfold uE in *. cbn [fst snd]. rewrite !esubst_denot, IH. reflexivity.
Qed.
#[using="e_sp0_init argH_agree"] Lemma inst_hid : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "Q3'Y='='Y@'S6'QL'Nv^<r4%3221'H'_2yR0%211'7pg@21&X:r6&TIr3r5%3321=r2%73621&XI&Y<%129B%33:71%<3196%C3>61p0E1pl4J1pjFL1pi@N1pS6Q01pR<Q21").
Proof.
intros E J e inv model HJ. apply functional_extensionality. intros a. unfold hid, vis.
rewrite inst_in_allow. rewrite (argH_agree E (upd E J (edenot E e)) a); [|eapply env_agree_le; [apply upd_agree | exact HJ]].
rewrite <- (utop_agree J E (upd E J (edenot E e)) (upd_agree _ _ _) HJ).
unfold inst. cbn [a_maps]. reflexivity.
Qed.
#[using="Type"] Lemma inst_maps : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "Q5'Y='='Y@'S6'H'<'B'_2yR0%211%4211%611&Q1'S<&X3r4%211&S3&TIr1r3r2%43321%611%<4;>81&XI&Y<%12<6%33=81%?11%=1;%C4BE21%L3E81pjFN1pi@Q01pS6Q21pR<Q41").
Proof.
intros. unfold inst. cbn [a_maps]. rewrite map_map. apply map_ext. intros m. unfold amap_den, msubst. cbn [am_base am_len].
rewrite !esubst_denot. reflexivity.
Qed.
Section SE.
Local Abbreviation SEC_T_maps_match_msubst := (ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "Q3'Y='='Y@'<'S<%211'B'_2yR0%211%4211%811&J&XDr5&Q1&V2r4r3%3221r2%64AA21r1%:3921&XI&Y<%12<8%33=:1%?3186%A261pk<C1pl8J1pi@N1pS6Q01pR<Q21")) (only parsing).
Variable E : ltac:(sec_ty2 constr:(SEC_T_maps_match_msubst) 0%nat 0%nat).
Variable J : ltac:(sec_ty2 constr:(SEC_T_maps_match_msubst) 1%nat 0%nat).
Variable e : ltac:(sec_ty2 constr:(SEC_T_maps_match_msubst) 2%nat 0%nat).
Lemma maps_match_msubst : ltac:(sec_stmt2 constr:(SEC_T_maps_match_msubst) 3%nat 0%nat).
Proof using Type E J e.
intros ms.
induction ms as [|m ms IH]; intros l; cbn [maps_match map]; [tauto|].
unfold is_fog, msubst, uE, amap_den. cbn [am_kind am_base am_len]. rewrite !esubst_denot.
destruct (is_tok_kind (am_kind m)).
- split; (intros [HM|(iv & l' & -> & Hsz & HM)]; [left; apply IH; exact HM | right; exists iv, l'; split; [reflexivity|]; split; [exact Hsz | apply IH; exact HM]]).
- split; (intros (l' & -> & HM); exists l'; split; [reflexivity | apply IH; exact HM]).
Qed.
End SE.
#[using="Type"] Lemma holes_msubst : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "Q9'Y='='Y@'Q3'<'B'_2yR0%211%4211%611'S<%811&J'Q0&X;r6r3r2%43321&Q1&V2r5r4%3221r1%64??21%=3@81&XI&Y<%12>7%33?91%A31?>%C3F18%E271pl8G1pk<J1po@Q21pi@Q41pS6Q61pR<Q81").
Proof.
intros E J e y l ms. induction ms as [|m ms IH]; cbn [map].
- split; intros; constructor.
- rewrite !Forall_cons_iff, IH.
assert (X : hole_ok E y l (msubst J e m) <-> hole_ok (upd E J (edenot E e)) y l m).
{ unfold hole_ok, is_hole, msubst, uE. cbn [am_kind am_base am_len]. rewrite !esubst_denot. tauto. }
rewrite X. tauto.
Qed.
#[using="Type"] Lemma inst_maps_match : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "Q3'Y='='Y@'S6'<'B'_2yR0%211%4211%611&J&XDr5&S3&TIr2r4r3%43321%611r1%:3921&XI&Y<%12<7%33=91%=1;%@3217%B271pk<D1pjFL1pi@N1pS6Q01pR<Q21").
Proof. intros. unfold inst. cbn [a_maps]. apply maps_match_msubst. Qed.
#[using="Type"] Lemma regs_ok_inst : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "Q2'Y='='Y@'<%112&R8y5'_2yR0%211%5241&J&Z7r5&Q1&T1r4r3%3221r2%64BB21r1%:3921&XI&Y<%12<8%33=:1%?3186%A261pTNC1pmLJ1pi@M1pS6O1pR<Q11").
Proof.
intros E J e sr R. unfold regs_ok, sr_get.
assert (G : forall r, edenot E (if bv_eqb r 0 then ELit 0 else nth (ridx r) (map (esubst J e) sr) (ELit 0))
= edenot (upd E J (edenot E e)) (if bv_eqb r 0 then ELit 0 else nth (ridx r) sr (ELit 0))).
{ intros r. destruct (bv_eqb r 0); [reflexivity|].
replace (ELit 0) with (esubst J e (ELit 0)) at 1 by reflexivity. rewrite map_nth. apply esubst_denot. }
split; intros H r; [rewrite <- G | rewrite G]; apply H.
Qed.
#[using="Type"] Lemma fds_ok_inst : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "J'Y='='Y@'S8'QL&J&X7r5&T:r4r3r2%43321r1%83721&XI&Y<%12:7%33;91%=3186%?261pl4A1piJC1pi@E1pS6G1pR<I1").
Proof.
intros E J e f model. destruct f as [|k l o|]; cbn [fsubst fds_ok]; try tauto.
unfold uE. rewrite !esubst_denot. cbn [eb upd]. tauto.
Qed.
#[using="Type"] Lemma hreplay_hsubst : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "Q1'Y='='Y@'<'T?%211'H'B'_2yR0%211%4211%911&X<r4&Q1&TEr3r2%3221r1%64AA21%9281&XI&Y<%12;7%33<91%>217%F3@61pj8H1pi@L1pS6N1pR<Q01").
Proof.
intros E J e h. induction h as [|[b n|b n] h IH]; [reflexivity| |]; cbn [map hsubst hreplay]; rewrite IH; unfold uE; rewrite !esubst_denot; reflexivity.
Qed.
#[using="e_sp0_init argH_agree SINV_agree"] Lemma cs_ok_inst : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "QI'Y='='Y@'S6&R8y5'_2yR0%211%5241'@y8%611%311p061'QL'Nv^<r6%3221'H'<'YM%211&YJ&S4r5%211%411(?%118%;3831&J'X4r9&TIr8r7%33D21r4r3%8573?21&XI&Y<%12:7%33;91%=51LD76%?261p0A1p0N1pl4Q31pRFQ51pTNQ;1pjFQB1pi@QD1pS6QF1pR<QH1").
Proof.
intros E J e inv R FULL model HJ Hlog.
pose proof (inst_hid E J e inv model HJ) as HH. pose proof (inst_allowA E J e inv) as HA. pose proof (inst_maps E J e inv) as HM.
pose proof (inst_in_ghost E J e inv) as HG.
assert (AG : env_agree nx0 E (upd E J (edenot E e))) by (eapply env_agree_le; [apply upd_agree | exact HJ]).
pose proof (utop_agree J E (upd E J (edenot E e)) (upd_agree _ _ _) HJ) as HU.
assert (HSP : uE (upd E J (edenot E e)) e_sp0 = uE E e_sp0).
{ unfold uE. rewrite (edenot_agree' nx0 E _ e_sp0 AG e_sp0_init). reflexivity. }
pose proof (sppg_agree J E (upd E J (edenot E e)) (upd_agree _ _ _) HJ) as HSG.
split; intros HC; destruct HC; constructor;
cbn [inst a_ss s_regs s_log s_know kn a_maps a_totsz a_ylo a_eager a_vis a_ghost a_abytes a_brk a_fd a_tidset a_hna a_hlz mk_ss] in *;
rewrite <- ?HA, <- ?HM, ?HU, ?HSP, ?HSG; rewrite ?HU, ?HSP, ?HSG in *; try assumption.
- apply regs_ok_inst. assumption.
- unfold Mr. rewrite <- HH. apply know_ok_ksubst. exact co_know0.
- apply fds_ok_inst. assumption.
- apply (proj1 (maps_match_msubst E J e _ _)). assumption.
- apply (proj1 (holes_msubst E J e _ _ _)). assumption.
- apply Forall_forall. intros m Hin Hk.
pose proof (proj1 (Forall_forall _ _) co_none0 (msubst J e m) ltac:(apply in_map; exact Hin) Hk) as X.
unfold amap_den, msubst in X |- *. cbn [am_base am_len am_kind] in X. rewrite !esubst_denot in X. exact X.
- apply Forall_forall. intros m Hin Hk a Ha.
pose proof (proj1 (Forall_forall _ _) co_kinds0 (msubst J e m) ltac:(apply in_map; exact Hin) Hk a) as X.
unfold msubst in X. cbn [am_base am_len] in X. rewrite !esubst_denot in X. exact (X Ha).
- rewrite <- esubst_denot. assumption.
- intros a. unfold Mr in *. rewrite <- HH. first [rewrite HG | rewrite <- HG]. exact (co_zero0 a).
- eapply SINV_agree; [exact AG | assumption].
- unfold RNA in *. rewrite <- hreplay_hsubst. assumption.
- unfold RLZ in *. rewrite <- hreplay_hsubst. assumption.
- apply regs_ok_inst. assumption.
- reflexivity.
- unfold Mr in *. rewrite HH. apply know_ok_ksubst. assumption.
- apply fds_ok_inst. assumption.
- apply (proj2 (maps_match_msubst E J e _ _)). assumption.
- apply (proj2 (holes_msubst E J e _ _ _)). assumption.
- apply Forall_forall. intros m' Hin Hk. apply in_map_iff in Hin as [m [<- Hin]].
pose proof (proj1 (Forall_forall _ _) co_none0 m Hin Hk) as X.
unfold amap_den, msubst. cbn [am_base am_len am_kind]. rewrite !esubst_denot. exact X.
- apply Forall_forall. intros m' Hin Hk a Ha. apply in_map_iff in Hin as [m [<- Hin]].
unfold msubst in Ha, Hk. cbn [am_base am_len am_kind] in Ha, Hk. rewrite !esubst_denot in Ha.
exact (proj1 (Forall_forall _ _) co_kinds0 m Hin Hk a Ha).
- rewrite esubst_denot. assumption.
- rewrite HA. assumption.
- rewrite HA. assumption.
- intros a. unfold Mr in *. rewrite HH. first [rewrite <- HG | rewrite HG]. exact (co_zero0 a).
- eapply SINV_agree; [|eassumption]. destruct AG as [AG1 AG2]. split; [intros n Hn; symmetry; apply AG1; exact Hn | symmetry; exact AG2].
- unfold RNA in *. rewrite hreplay_hsubst. assumption.
- unfold RLZ in *. rewrite hreplay_hsubst. assumption.
Qed.
Section SE.
Local Abbreviation SEC_T_kentry_eqb_h_sound := (ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "Q:'Y='_2yR0%211'@y8%511%311p051'<'YE%211&Z6vZJr5r4r3%544321&Z5r6%247164'H'7&U1%1298(D%53421&U4%129=%83714r9r8%>4C21Bp041p081p0?1p0C1pS8K1pg6L1pk0L1pTDQ01pR<Q91")) (only parsing).
Variable E : ltac:(sec_ty2 constr:(SEC_T_kentry_eqb_h_sound) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_kentry_eqb_h_sound) 1%nat 0%nat).
Variable k : ltac:(sec_ty2 constr:(SEC_T_kentry_eqb_h_sound) 2%nat 0%nat).
Lemma kentry_eqb_h_sound : ltac:(sec_stmt2 constr:(SEC_T_kentry_eqb_h_sound) 3%nat 0%nat).
Proof using Type E M k.
intros X K HK HX Heq Hfl.
unfold kentry_eqb_h in Heq. apply orb_prop in Heq as [Heq|Heq].
{ apply kentry_eqb_eq in Heq. subst. exact HX. }
assert (SAD : forall b o b' o' n ne, saddr_eqb_h (SA b o) (SA b' o') = true -> flat E (SA b o) n ->
flat_x k b' o' ne = true -> estart E (SA b' o') = estart E (SA b o)).
{ intros b o b' o' n ne Hs Hf Hf'. unfold saddr_eqb_h in Hs. cbn [a_base a_off] in *.
apply orb_prop in Hs as [Hs|Hs]; [apply saddr_eqb_eq in Hs; injection Hs as -> ->; reflexivity|].
apply expr_eqb_eq in Hs. apply (f_equal (fun x => bv_unsigned (edenot E x))) in Hs.
unfold eaddz in Hs. rewrite !mkAlu_denot, !u_add64 in Hs. cbn [edenot] in Hs. rewrite !u_lit64 in Hs.
pose proof (flat_x_sound E M k b' o' ne HK Hf') as (F1 & F2 & F3). pose proof (u64_range (edenot E ne)).
unfold flat, estart in *; cbn [a_base a_off] in *.
pose proof (u64_range (edenot E b)). pose proof (u64_range (edenot E b')). unfold two64 in Hs.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
assert (E1 : (bv_unsigned (edenot E b) + o mod 2 ^ 64) mod 2 ^ 64 = bv_unsigned (edenot E b) + o) by (rewrite Zplus_mod_idemp_r; apply Z.mod_small; lia).
assert (E2 : (bv_unsigned (edenot E b') + o' mod 2 ^ 64) mod 2 ^ 64 = bv_unsigned (edenot E b') + o') by (rewrite Zplus_mod_idemp_r; apply Z.mod_small; lia).
lia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
assert (AD : forall a a', estart E a' = estart E a -> adenot E a' = adenot E a).
{ intros [b o] [b' o'] He. unfold adenot, estart, v_addi in *. cbn [a_base a_off] in *. apply bv_eq. rewrite !Z_to_bv_unsigned. rewrite He. reflexivity. }
destruct X as [[b o] w v|[b o] n|[b o] n kk| | | |[b o] n| |[b o] n c|[b o] n];
destruct K as [[b' o'] w' v'|[b' o'] n'|[b' o'] n' kk'| | | |[b' o'] n'| |[b' o'] n' c'|[b' o'] n']; try discriminate;
repeat match type of Heq with (_ && _)%bool = true => apply andb_prop in Heq as [Heq ?X] end;
cbn [kentry_ok kflat_h] in *.
- apply Nat.eqb_eq in X0. apply expr_eqb_eq in X. subst w' v'. destruct HX as (H1 & H2 & H3).
pose proof (SAD b o b' o' _ _ Heq H2 Hfl) as ES.
split; [exact H1|]. split; [unfold flat in *; rewrite ES; exact H2|]. rewrite (AD _ _ ES). exact H3.
- apply expr_eqb_eq in X. subst n'. destruct HX as [H1 H2].
pose proof (SAD b o b' o' _ _ Heq H1 Hfl) as ES. split; [unfold flat in *; rewrite ES; exact H1|]. rewrite ES. exact H2.
- apply Nat.eqb_eq in X. apply expr_eqb_eq in X0. subst n' kk'. destruct HX as (H1 & H2 & H3).
pose proof (SAD b o b' o' _ _ Heq H1 Hfl) as ES. split; [unfold flat in *; rewrite ES; exact H1|]. rewrite ES. split; [exact H2 | exact H3].
- apply expr_eqb_eq in X. subst n'. destruct HX as [H1 H2].
pose proof (SAD b o b' o' _ _ Heq H1 Hfl) as ES. split; [unfold flat in *; rewrite ES; exact H1|]. rewrite ES. exact H2.
- apply Z.eqb_eq in X. apply expr_eqb_eq in X0. subst n' c'. destruct HX as [H1 H2].
pose proof (SAD b o b' o' _ _ Heq H1 Hfl) as ES. split; [unfold flat in *; rewrite ES; exact H1|]. rewrite ES. exact H2.
- apply expr_eqb_eq in X. subst n'. destruct HX as [H1 H2].
pose proof (SAD b o b' o' _ _ Heq H1 Hfl) as ES. split; [unfold flat in *; rewrite ES; exact H1|]. rewrite ES. exact H2.
Qed.
End SE.
#[using="SEGS_in_hull"] Lemma seg_rom_off_hull : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "J'_2yR0%211'H'7&XMv0&_3r1%2281%5241(9%93821'@y8%?11%311&ZBvZJr2%3221(1%117%D3731p0<1pg@G1").
Proof.
intros a Ha. unfold seg_rom.
rewrite (memory_read1_hidden SEGS (fun x => negb (in_hull A (bv_unsigned x)))); [reflexivity| |].
- intros x Hx. apply SEGS_in_hull. apply negb_true_iff in Hx. exact Hx.
- rewrite Ha. reflexivity.
Qed.
#[using="SEGS_in_hull"] Lemma rdn_bytes_some : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "QK'_2yR0%211'@y8%511%311p051'='<%115'H%912&Z@vZJr4r3r2%544321(4r1%22;1%;3:41'G&[3&_3r5%22J1%32K8%5221&[4&[1&[7%11B%3271%5271%=271'7&XMv0%?2Q7G%3221(9%Q03621&Kr8%11N(1%11Q;%Q63Q;31%611p081p0@1po>QC1p0Q01ph4Q=1po4Q@1pg@QG1pTDQC1").
Proof.
intros M a w. revert a. induction w as [|w IH]; intros a bs Hr x Hx Hh; [lia|].
cbn [rdn] in Hr.
destruct (Z.eq_dec (bv_unsigned x) (bv_unsigned a)) as [Heq|Hne].
- assert (x = a) by (apply bv_eq; exact Heq). subst x.
destruct (M a) eqn:HMa; [congruence|]. rewrite (seg_rom_off_hull a Hh) in Hr. discriminate.
- destruct (match M a with Some b => Some b | None => seg_rom SEGS a end) as [b|]; [|discriminate].
destruct (rdn SEGS M (a + 1)%bv w) as [rest|] eqn:Hr2; [|discriminate].
pose proof (u64_range x).
assert (Hu1 : bv_unsigned (a + 1)%bv = (bv_unsigned a + 1)%Z) by (apply u_add1; lia).
eapply (IH (a + 1)%bv rest Hr2); [rewrite Hu1; lia | exact Hh].
Qed.
Section SE.
Local Abbreviation SEC_T_cover1_sound := (ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "RB'Y='_2yR0%211'@y8%511%311p051'<'YE%211'Y@'Q3&Z6vZJr6r5r4%544321'H%A18&SAr3%23761(4r2%22>1%83741'G&[4%12=8&[3r1%22A1%522A%7221'7&XMv0&[1&Y1r:r7%3221%521C%8271(9%L3;21zr;r8%;221%=21N%F251&[9+2+R0%3221%M261%O261&K&_1%12QM:%F11(1%11QL%Q?3QL31%711%Q8291p0F1p0Q31pjLQK1%Q<2Q:1p0Q>1p0QH1pi@QO1pjBR01pgFR21pk0R41pTDR81pR<RA1")) (only parsing).
Variable E : ltac:(sec_ty2 constr:(SEC_T_cover1_sound) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_cover1_sound) 1%nat 0%nat).
Lemma cover1_sound : ltac:(sec_stmt2 constr:(SEC_T_cover1_sound) 2%nat 0%nat).
Proof using SEGS_in_hull E M.
intros k b i e HK.
induction k as [|K r IH]; intros H; [discriminate|].
inversion HK as [|K' r' HKK Hr]; subst. cbn [cover1] in H.
match type of H with (match ?h with Some e0 => Some e0 | None => _ end = _) => destruct h as [e1|] eqn:Hhit end;
[injection H as <- | exact (IH Hr H)].
clear IH Hr HK.
assert (ZF : forall kb kk l (P : option byte -> Prop),
(flat E (SA kb kk) (elenZ E (ELit l)) /\ forall i0, (0 <= i0 < elenZ E (ELit l))%Z -> P (M (Z_to_bv 64 (estart E (SA kb kk) + i0)))) ->
(forall x, P x -> x <> None) ->
(if (expr_eqb b kb && Z.leb 0 l && Z.ltb l two64 && Z.leb kk i && Z.ltb i (kk + l))%bool then Some (kk + l)%Z else None) = Some e1 ->
(i < e1)%Z /\ forall j, (i <= j < e1)%Z -> in_hull A (uE E b + j) = false ->
(0 <= uE E b + j < 2 ^ 64)%Z /\ M (Z_to_bv 64 (uE E b + j)) <> None).
{ intros kb kk l P [Hfl Hall] HP Hc.
destruct (expr_eqb b kb && Z.leb 0 l && Z.ltb l two64 && Z.leb kk i && Z.ltb i (kk + l))%bool eqn:Hcnd; [|discriminate].
injection Hc as <-.
repeat match type of Hcnd with (_ && _)%bool = true => apply andb_prop in Hcnd as [Hcnd ?X] end.
apply expr_eqb_eq in Hcnd. subst kb. apply Z.leb_le in X2. apply Z.ltb_lt in X1. apply Z.leb_le in X0. apply Z.ltb_lt in X.
unfold two64 in X1. rewrite (elenZ_lit E l) in Hfl, Hall by lia.
destruct Hfl as (F1 & F2 & F3 & F4). unfold estart in *; cbn [a_base a_off] in *. unfold uE.
split; [lia|]. intros j Hj Hh. split; [lia|].
replace (bv_unsigned (edenot E b) + j)%Z with (bv_unsigned (edenot E b) + kk + (j - kk))%Z by lia.
apply HP. apply Hall. lia. }
destruct K as [[kb kk] w v|[kb kk] [l| | | | | | |]|[kb kk] [l| | | | | | |] bk| | | | | |[kb kk] [l| | | | | | |] fc|[kb kk] [l| | | | | | |]];
try discriminate.
-
destruct (expr_eqb b kb && Z.leb kk i && Z.ltb i (kk + Z.of_nat w))%bool eqn:Hcnd; [|discriminate]. injection Hhit as <-.
apply andb_prop in Hcnd as [Hcnd X]. apply andb_prop in Hcnd as [Hb X0].
apply expr_eqb_eq in Hb. subst kb. apply Z.leb_le in X0. apply Z.ltb_lt in X.
cbn [kentry_ok] in HKK. destruct HKK as (Hw & Hfl & Hrd).
pose proof (flat_u E _ _ Hfl) as Hu. destruct Hfl as (F1 & F2 & F3 & F4). unfold estart in *; cbn [a_base a_off] in *. unfold uE.
split; [lia|]. intros j Hj Hh. split; [lia|].
apply (rdn_bytes_some M _ w _ Hrd); rewrite ?Hu, ?u64_lit by lia; [lia | exact Hh].
- eapply (ZF kb kk l (fun x => x = Some (Z_to_bv 8 0))); [exact HKK | intros x ->; discriminate | exact Hhit].
- cbn [kentry_ok] in HKK. destruct HKK as (Hfl & Hlen & Hall).
eapply (ZF kb kk l (fun x => exists b0, x = Some b0)); [split; [exact Hfl | intros i0 Hi0; eexists; apply Hall; exact Hi0] | intros x [b0 ->]; discriminate | exact Hhit].
- eapply (ZF kb kk l (fun x => x = Some (Z_to_bv 8 fc))); [exact HKK | intros x ->; discriminate | exact Hhit].
- eapply (ZF kb kk l (fun x => x <> None)); [exact HKK | intros x Hx; exact Hx | exact Hhit].
Qed.
End SE.
#[using="SEGS_in_hull"] Lemma cover_x_sound : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "R@'='Y='_2yR0%211'@y8%511%311p051'<'YE%211'Y@'Q3&Z6vZJr6r5r4%544321'H'7&SBr8r3r2%4539821(D%83721'G&[3r1%22?1&[4%123@%6231&XMv0&[1&Y1r:r7%3221%521B%8271(9%J3I21zr;%:21J%<21J%E241&[9+2+R0%3221%G261%L261&K&_1%12QJ:%E11(1%11QI%Q<3QI31%711%Q5291p0E1p0Q11pjLQH1p0Q:1p0QD1pn:QK1pjBQL1pgFQN1pk0R01pTDR41pR<R=1pj0R?1").
Proof.
induction fuel as [|f IH]; intros E M k b i stop HK H j Hj Hh; [discriminate|].
cbn [cover_x] in H. destruct (Z.leb_spec stop i); [lia|].
destruct (cover1 k b i) as [e|] eqn:Hc; [|discriminate].
destruct (Z.ltb_spec i e); [|discriminate].
destruct (cover1_sound E M k b i e HK Hc) as [_ Hcov].
destruct (Z.lt_ge_cases j e).
- apply Hcov; [lia | exact Hh].
- eapply IH; [exact HK | exact H | lia | exact Hh].
Qed.
Section SE.
Local Abbreviation SEC_T_kunk_covered_sound := (ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "Q3'Y='_2yR0%211'@y8%511%311p051'<'YE%211&Z6vZJr4r3r2%544321'H'7&U@v0%23176(D%63521&Z5r6r5%34?21=p051p0=1pS8E1pk0E1pTDI1pR<Q21")) (only parsing).
Variable E : ltac:(sec_ty2 constr:(SEC_T_kunk_covered_sound) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_kunk_covered_sound) 1%nat 0%nat).
Variable k : ltac:(sec_ty2 constr:(SEC_T_kunk_covered_sound) 2%nat 0%nat).
Lemma kunk_covered_sound : ltac:(sec_stmt2 constr:(SEC_T_kunk_covered_sound) 3%nat 0%nat).
Proof using SEGS_in_hull HULL_ok E M k.
intros K HK H.
unfold kunk_covered in H.
destruct K as [| | | | | | | | |[b o] [n| | | | | | |]]; try discriminate.
repeat match type of H with (_ && _)%bool = true => apply andb_prop in H as [H ?X] end.
apply Z.ltb_lt in H. apply Z.leb_le in X3. apply Z.leb_le in X2.
pose proof (flat_x_sound E M k b o (ELit n) HK X1) as (F1 & F2 & F3).
pose proof (ranges_apart_x_sound SEGS E M k _ _ _ _ _ _ HK X0) as AP0.
cbn [edenot] in F2, F3. rewrite u64_lit in F2, F3 by lia.
pose proof HULL_ok as HU; unfold hull_ok, KHI in HU.
rewrite (elenZ_lit E n) in AP0 by lia. rewrite (elenZ_lit E (img_hi A - img_lo A)) in AP0 by lia.
unfold estart in AP0; cbn [a_base a_off edenot] in AP0. rewrite u_lit0 in AP0.
cbn [kentry_ok]. rewrite elenZ_lit by lia. split.
- unfold flat, estart in *; cbn [a_base a_off] in *. lia.
- intros i Hi. unfold estart in *; cbn [a_base a_off] in *.
replace (bv_unsigned (edenot E b) + o + i)%Z with (uE E b + (o + i))%Z by (unfold uE; lia).
apply (cover_x_sound _ E M k b o (o + n) HK X); [lia|].
unfold in_hull, uE. apply andb_false_iff.
destruct AP0 as [AP0|AP0]; [left; apply Z.leb_gt; lia | right; apply Z.ltb_ge; lia].
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_kn_incl_h_sound := (ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "Q2'Y='_2yR0%211'@y8%511%311p051'<'YE%211&Z6vZJr4r3r2%544321'H'7&U<v0%23176(D%63521r6r5%?4>21<p041p0<1pnDC1pk0D1pTDH1pR<Q11")) (only parsing).
Variable E : ltac:(sec_ty2 constr:(SEC_T_kn_incl_h_sound) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_kn_incl_h_sound) 1%nat 0%nat).
Variable k : ltac:(sec_ty2 constr:(SEC_T_kn_incl_h_sound) 2%nat 0%nat).
Variable tk : ltac:(sec_ty2 constr:(SEC_T_kn_incl_h_sound) 3%nat 0%nat).
Lemma kn_incl_h_sound : ltac:(sec_stmt2 constr:(SEC_T_kn_incl_h_sound) 4%nat 0%nat).
Proof using SEGS_in_hull HULL_ok E M k tk.
intros HK H.
unfold kn_incl_h in H. apply Forall_forall. intros K Hin.
pose proof (proj1 (forallb_forall _ _) H K Hin) as HK1. unfold kn_incl1_h in HK1.
destruct (existsb (fun X => kentry_eqb X K) k) eqn:Hex1.
{ apply existsb_exists in Hex1 as [X [HinX Heq]]. apply kentry_eqb_eq in Heq. subst. exact (proj1 (Forall_forall _ _) HK K HinX). }
assert (IMG : kimg_sub_covered k K = true -> kentry_ok SEGS E M K).
{ intros Hc. unfold kimg_sub_covered in Hc. destruct K as [| | |lo hi| | | | | |]; try discriminate.
apply existsb_exists in Hc as [X [HinX HX]]. destruct X as [| | |lo' hi'| | | | | |]; try discriminate.
apply andb_prop in HX as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
pose proof (proj1 (Forall_forall _ _) HK _ HinX) as HKX. cbn [kentry_ok] in HKX |- *.
destruct HKX as (Ha & Hb & Hc). split; [lia|]. split; [lia|]. intros i Hi. apply Hc. lia. }
destruct (kflat_h k K) eqn:Hfl.
- destruct (existsb (fun X => kentry_eqb_h X K) k) eqn:Hex.
+ apply existsb_exists in Hex as [X [HinX Heq]].
eapply kentry_eqb_h_sound; [exact HK | exact (proj1 (Forall_forall _ _) HK X HinX) | exact Heq | exact Hfl].
+ destruct (kimg_sub_covered k K) eqn:Himg; [exact (IMG eq_refl)|]. eapply kunk_covered_sound; [exact HK | exact HK1].
- destruct (kimg_sub_covered k K) eqn:Himg; [exact (IMG eq_refl)|]. eapply kunk_covered_sound; [exact HK | exact HK1].
Qed.
End SE.
Definition is_havoc (lo hi : nat) (t : expr) : option nat :=
match t with EVar v => if (Nat.leb lo v && Nat.ltb v hi)%bool then Some v else None | _ => None end.
Fixpoint henv (lo hi : nat) (E : env) (rs ts : list expr) : env :=
match rs, ts with
| r :: rs', t :: ts' =>
let E1 := henv lo hi E rs' ts' in
match is_havoc lo hi t with Some v => upd E1 v (edenot E r) | None => E1 end
| _, _ => E
end.
#[using="Type"] Lemma is_havoc_range : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "N'='Y@'H'@%114&X?r4r3r2%43321(4r1%22<1%;3941'G(Y4%118%?3@:1'Nr5%221<&O%12>@%9231%:271p0<1po0J1pn@J1pj<L1pkHM1").
Proof.
intros lo hi t v H. destruct t; try discriminate. cbn [is_havoc] in H.
destruct (Nat.leb lo n && Nat.ltb n hi)%bool eqn:Hc; [|discriminate]. injection H as <-.
apply andb_prop in Hc as [H1 H2]. apply Nat.leb_le in H1. apply Nat.ltb_lt in H2. split; [reflexivity | lia].
Qed.
#[using="Type"] Lemma henv_agree : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "C'='Y='<'Y@%211&Z9r5r3&X9r4r2r1%4563521%83761pnH:1pm>;1pR<?1pj<A1pkHB1").
Proof.
intros lo hi E rs. induction rs as [|r rs IH]; intros [|t ts]; cbn [henv]; try apply env_agree_refl.
destruct (is_havoc lo hi t) as [v|] eqn:Hv; [|apply IH].
apply is_havoc_range in Hv as [_ Hv]. eapply env_agree_trans; [apply IH|]. eapply env_agree_le; [apply upd_agree | lia].
Qed.
#[using="Type"] Lemma henv_high : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "O'='Y='<'Y@%211'Nr5r1%3221'H'_2yR0%211&Y?&X9r7r6r4r3%5543=21r2%8221%92@2%>3;21p0@1pl:I1pnHF1pm>G1pR<K1pj<M1pkHN1").
Proof.
intros lo hi E rs. induction rs as [|r rs IH]; intros [|t ts] n Hn; cbn [henv]; try reflexivity.
destruct (is_havoc lo hi t) as [v|] eqn:Hv; [|apply IH; exact Hn].
apply is_havoc_range in Hv as [_ Hv]. cbn [upd ev]. destruct (Nat.eqb_spec n v); [lia|]. apply IH. exact Hn.
Qed.
Section SE.
Local Abbreviation SEC_T_regs_match_h_char := (ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "R@'='<%112'Y@%311'H'7&W0r5r4r3r2r1%6554321(D%:3921'G&;%12?8%22@8%?3D21&O%12:4'L'I'@%11J&X?r9r8&Q2(Y2z%211%44OHJ1%83761(4%12Q5I%Q13<31&K&ZKr7%23Q:N1%411%G2Q0Q3r;r:%A4Q<Q46>%E3321%=2QAQ7%Q=3H21%<11p081pjDQE1%Q62;1%Q72A1qo0QH1%Q12QI1%L4QGQ?QAI%Q03NB1(1%11QM%QI3Q431%Q14QLQDQGN%QK3QM61&T3%12Q58%QN3QM1QE%QD241%QE271%Q?2=1p0QA1pjBR81%QI2QE1p0QK1pnHR71pm>R81pmFR;1pj<R>1pkHR?1")) (only parsing).
Variable lo : ltac:(sec_ty2 constr:(SEC_T_regs_match_h_char) 0%nat 0%nat).
Variable hi : ltac:(sec_ty2 constr:(SEC_T_regs_match_h_char) 1%nat 0%nat).
Variable seen : ltac:(sec_ty2 constr:(SEC_T_regs_match_h_char) 2%nat 0%nat).
Lemma regs_match_h_char : ltac:(sec_stmt2 constr:(SEC_T_regs_match_h_char) 3%nat 0%nat).
Proof using Type lo hi seen.
intros rs.
revert seen. induction rs as [|r rs IH]; intros seen [|t ts] H; cbn [regs_match_h length] in H |- *; try discriminate.
- split; [reflexivity | intros i Hi; lia].
- assert (STEP : forall seen', regs_match_h lo hi seen' rs ts = true -> (forall v, In v seen -> In v seen') ->
(forall v, is_havoc lo hi t = Some v -> In v seen') ->
length rs = length ts /\ forall i, (Datatypes.S i < Datatypes.S (length ts))%nat ->
(exists v, is_havoc lo hi (nth (Datatypes.S i) (t :: ts) (ELit 0)) = Some v /\ ~ In v seen /\
forall i', (i' < Datatypes.S i)%nat -> is_havoc lo hi (nth i' (t :: ts) (ELit 0)) <> Some v)
\/ (is_havoc lo hi (nth (Datatypes.S i) (t :: ts) (ELit 0)) = None /\ nth (Datatypes.S i) (t :: ts) (ELit 0) = nth (Datatypes.S i) (r :: rs) (ELit 0)
/\ APK.expr_vars_lt lo (nth (Datatypes.S i) (t :: ts) (ELit 0)) = true)).
{ intros seen' Hm Hsub Ht. destruct (IH seen' ts Hm) as [Hlen Hc]. split; [exact Hlen|].
intros i Hi. cbn [nth]. destruct (Hc i ltac:(lia)) as [[v (Hv & Hns & Hbefore)]|Hn]; [left|right; exact Hn].
exists v. split; [exact Hv|]. split; [intros Hin; apply Hns; apply Hsub; exact Hin|].
intros [|i'] Hi'; cbn [nth].
- intros Heq. apply Hns. apply Ht. exact Heq.
- apply Hbefore. lia. }
destruct (is_havoc lo hi t) as [v|] eqn:Hv.
+ destruct t as [|w| | | | | |]; try discriminate. cbn [is_havoc] in Hv.
destruct (Nat.leb lo w && Nat.ltb w hi)%bool eqn:Hr; [|discriminate]. injection Hv as Hwv. subst v.
apply andb_prop in H as [Hnew Hm]. apply negb_true_iff in Hnew.
assert (Hns : ~ In w seen).
{ intros Hin. enough (existsb (Nat.eqb w) seen = true) by congruence. apply existsb_exists. exists w. split; [exact Hin | apply Nat.eqb_refl]. }
destruct (STEP (w :: seen) Hm ltac:(intros; right; assumption) ltac:(intros v' Hv'; injection Hv' as <-; left; reflexivity)) as [Hlen Hc].
split; [rewrite Hlen; reflexivity|]. intros [|i] Hi; [|exact (Hc i Hi)].
left. exists w. cbn [nth is_havoc]. rewrite Hr. split; [reflexivity|]. split; [exact Hns|]. intros i' Hi'. lia.
+ assert (Hm : (expr_eqb r t && APK.expr_vars_lt lo t && regs_match_h lo hi seen rs ts)%bool = true).
{ destruct t; try exact H. cbn [is_havoc] in Hv. destruct (Nat.leb lo n && Nat.ltb n hi)%bool; [discriminate | exact H]. }
apply andb_prop in Hm as [Hm1 Hm]. apply andb_prop in Hm1 as [He Hvl]. apply expr_eqb_eq in He. subst t.
destruct (STEP seen Hm ltac:(intros; assumption) ltac:(intros v' Hv'; discriminate Hv')) as [Hlen Hc].
split; [rewrite Hlen; reflexivity|]. intros [|i] Hi; [|exact (Hc i Hi)].
right. cbn [nth]. split; [exact Hv|]. split; [reflexivity | exact Hvl].
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_henv_havoc := (ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "R3'='Y='<'Y@%211'H&;r4%2251r3%4271%63;31&O%1245'@%11?&X?r9r8&Q2r5(Y2z%211%54EA41%93871(4%12KB%G3=31r1r6%C221&Kr<r;r2%A4Q11B=%E3431%<2Q68%Q23H21%811p0:1pjDQ:1'_2yR0%211&Y?&X9r:r7%35@2Q1Q01%521O&Y<%Q24QBGQ3N%22Q51%QB3:41p0>1p0M1p0Q=1p0Q@1po0QL1pjBQM1pnHQJ1pm>QK1pR<QO1pj<R11pkHR21")) (only parsing).
Variable lo : ltac:(sec_ty2 constr:(SEC_T_henv_havoc) 0%nat 0%nat).
Variable hi : ltac:(sec_ty2 constr:(SEC_T_henv_havoc) 1%nat 0%nat).
Variable E : ltac:(sec_ty2 constr:(SEC_T_henv_havoc) 2%nat 0%nat).
Lemma henv_havoc : ltac:(sec_stmt2 constr:(SEC_T_henv_havoc) 3%nat 0%nat).
Proof using Type lo hi E.
intros rs.
induction rs as [|r rs IH]; intros [|t ts] i v Hlen Hi Hv Hbefore; cbn [length] in *; try lia.
cbn [henv]. destruct i as [|i]; cbn [nth] in *.
- rewrite Hv. apply upd_at.
- destruct (is_havoc lo hi t) as [v'|] eqn:Ht.
+ cbn [upd ev]. destruct (Nat.eqb_spec v v').
* subst v'. exfalso. exact (Hbefore 0%nat ltac:(lia) Ht).
* apply IH; [lia | lia | exact Hv |]. intros i' Hi'. exact (Hbefore (Datatypes.S i') ltac:(lia)).
+ apply IH; [lia | lia | exact Hv |]. intros i' Hi'. exact (Hbefore (Datatypes.S i') ltac:(lia)).
Qed.
End SE.
#[using="Type"] Lemma regs_match_h_sound : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "Q='='Y='<'Y@%211&R8y5'_2yR0%211%5241'H'7&W0r6r5(?%11Ar3r2%7565321(D%;3:21&;%12E6uQ0%?3J21&Z7%13>=:&X9r9r8r7%45321CBr4%832D1p081p0;1p0@1pTNM1pnHQ41pm>Q51pR<Q91pj<Q;1pkHQ<1").
Proof.
intros lo hi E rs ts R H Hlen HR. destruct (regs_match_h_char lo hi [] rs ts H) as [Hl Hc].
intros r. unfold sr_get. destruct (bv_eqb r 0) eqn:Hr0; [exact (eq_trans (HR r) ltac:(unfold sr_get; rewrite Hr0; reflexivity))|].
pose proof (ridx_range r) as Hlt. specialize (HR r). unfold sr_get in HR. rewrite Hr0 in HR. rewrite HR.
destruct (Hc (ridx r) ltac:(lia)) as [[v (Hv & _ & Hbefore)]|(Hn & Heq & Hvl)].
- destruct (is_havoc_range _ _ _ _ Hv) as [Et _]. rewrite Et. cbn [edenot]. symmetry. apply (henv_havoc lo hi E rs ts (ridx r) v Hl ltac:(lia) Hv Hbefore).
- rewrite Heq in Hvl |- *. eapply (edenot_agree' lo); [apply henv_agree | exact Hvl].
Qed.
#[using="e_sp0_init argH_agree SINV_agree"] Lemma cs_ok_reenv : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "S;'='Y='S6'<'Y@%211&R8y5'_2yR0%211%5241'@y8%611%311p061'QL'X4r7r5r3r2r1%6554321&Z9r9r8%33219'Nv^<r:%3221'H'7&U=r;&U7%11;%4231(D%83721&UJr<&S3%11C%4231%>3=17&VKr=&6'B%12Q@Q@&S5%11G&S0%11I%73531%:291%J3I1C&T3r>&RN%11K%4231%Q03O1I&T5r?&RO%11J%4231%Q63Q51O&T=r@&S2%11J%4231%Q<3Q;1Q5rA&S1%11C%9231%QA3Q@1Q:&Z7%13;GQ3&W9%12=C%R5591JQ6Q<p041p071p0=1p0D1p0K1p0Q21p0Q?1p0QF1p0R01p0R51p0R:1pl4RB1pRFRD1pTNRJ1pmNS11phNS51pR>S71pR<S81pgFS:1").
Proof.
intros b E E' cs sr' R FULL model HC Hag Hb Hkn Hmaps Hallow Hbrk Hfd Hhna Hhlz HR.
pose proof (hid_agree b E E' cs model Hag Hb Hallow) as HH.
rewrite <- (hid_ext E' cs (set_regs cs sr') model eq_refl) in HH.
pose proof (allowA_agree b E E' cs Hag Hallow) as HA.
assert (HA2 : allowA E' (set_regs cs sr') = allowA E' cs) by reflexivity. rewrite <- HA2 in HA. clear HA2.
pose proof (utop_agree b E E' Hag Hb) as HU.
assert (HSP : uE E' e_sp0 = uE E e_sp0).
{ unfold uE. rewrite (edenot_agree' nx0 E E' e_sp0 (env_agree_le _ _ _ _ Hag Hb) e_sp0_init). reflexivity. }
pose proof (sppg_agree b E E' Hag Hb) as HSG.
destruct HC; constructor; cbn [set_regs with_ss a_ss mk_ss s_regs s_log s_know kn a_maps a_totsz a_ylo a_eager a_vis a_ghost a_abytes a_brk a_fd a_tidset a_hna a_hlz] in *;
rewrite ?HA, ?HU, ?HSP, ?HSG; try assumption; try reflexivity.
- unfold Mr in *. rewrite HH. eapply know_ok_agree'; eassumption.
- eapply fds_ok_agree; eassumption.
- eapply maps_match_agree; [exact Hag | exact Hmaps | assumption].
- eapply holes_agree; [exact Hag | exact Hmaps | assumption].
- apply Forall_forall. intros m Hin Hk.
pose proof (proj1 (forallb_forall _ _) Hmaps m Hin) as Hm. apply andb_prop in Hm as [H1 H2].
unfold amap_den. rewrite <- (edenot_agree' b E E' _ Hag H1), <- (edenot_agree' b E E' _ Hag H2).
exact (proj1 (Forall_forall _ _) co_none0 m Hin Hk).
- apply Forall_forall. intros m Hin Hk a Ha.
pose proof (proj1 (forallb_forall _ _) Hmaps m Hin) as Hm. apply andb_prop in Hm as [H1 H2].
rewrite <- (edenot_agree' b E E' _ Hag H1), <- (edenot_agree' b E E' _ Hag H2) in Ha.
exact (proj1 (Forall_forall _ _) co_kinds0 m Hin Hk a Ha).
- rewrite <- (edenot_agree' b E E' _ Hag Hbrk). assumption.
- intros a. rewrite HH. change (in_ghost E' (set_regs cs sr')) with (in_ghost E' cs). rewrite (in_ghost_agree b E E' cs Hag Hallow). exact (co_zero0 a).
- eapply SINV_agree; [eapply env_agree_le; [exact Hag | exact Hb] | assumption].
- unfold RNA in *. rewrite (hreplay_agree b E E' _ Hag Hhna). assumption.
- unfold RLZ in *. rewrite (hreplay_agree b E E' _ Hag Hhlz). assumption.
Qed.
Section SE.
Local Abbreviation SEC_T_entails_h_sound := (ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "RA'='Y='S6&R8y5'_2yR0%211%5241'@y8%611%311p061'QL'X4r6r5r3r2r1%6554321'H'7&SOv0r9r8%45321<;(D%83721'Nv^<r:%3221&;'Y@&YK&S4r7%211%411%7261uQ0%F3Q<21'I'G&Z9r=r;%3321N%D23O&Y?%12Q3Q2%226Q3%Q13Q@21p051pl:QI1%Q;5Q6Q0OCQ:'Q3&VL%11Q3%21M%Q93421%B261%C281%D2@1qR>R21%G2R31p0I1p0Q41p0Q91p0QC1pl4QK1pRFQM1pTNR31pfHR:1phNR;1pR<R=1pj<R?1pkHR@1")) (only parsing).
Variable lo : ltac:(sec_ty2 constr:(SEC_T_entails_h_sound) 0%nat 0%nat).
Variable hi : ltac:(sec_ty2 constr:(SEC_T_entails_h_sound) 1%nat 0%nat).
Variable E : ltac:(sec_ty2 constr:(SEC_T_entails_h_sound) 2%nat 0%nat).
Variable cs : ltac:(sec_ty2 constr:(SEC_T_entails_h_sound) 3%nat 0%nat).
Lemma entails_h_sound : ltac:(sec_stmt2 constr:(SEC_T_entails_h_sound) 4%nat 0%nat).
Proof using SEGS_in_hull HULL_ok e_sp0_init argH_agree SINV_agree lo hi E cs.
intros T R FULL model HC H Hlo Hlen.
unfold entails_h in H.
repeat match type of H with (_ && _)%bool = true => apply andb_prop in H as [H ?X] end.
rename H into Hpc. apply Z.eqb_eq in Hpc.
match goal with Hl : match s_log (a_ss T) with _ => _ end = true |- _ => rename Hl into HL; destruct (s_log (a_ss T)) eqn:HL'; [clear HL; rename HL' into HL|discriminate] end.
match goal with Hl : match s_resv (a_ss T) with _ => _ end = true |- _ => rename Hl into HRV; destruct (s_resv (a_ss T)) eqn:HRV'; [discriminate|clear HRV; rename HRV' into HRV] end.
match goal with Hr : regs_match_h _ _ _ _ _ = true |- _ => rename Hr into Hregs end.
match goal with Hm : list_eqb amap_eqb _ _ = true |- _ => apply (list_eqb_eq amap_eqb amap_eqb_eq) in Hm; rename Hm into Hmaps end.
match goal with Ha : list_eqb pair_eqb (a_vis cs) _ = true |- _ => apply (list_eqb_eq pair_eqb pair_eqb_eq) in Ha; rename Ha into Hallow end.
match goal with Hg : list_eqb pair_eqb (a_ghost cs) _ = true |- _ => apply (list_eqb_eq pair_eqb pair_eqb_eq) in Hg; rename Hg into Hghost end.
match goal with Hb : expr_eqb (a_brk cs) _ = true |- _ => apply expr_eqb_eq in Hb; rename Hb into Hbrk end.
match goal with Hf : afd_eqb _ _ = true |- _ => apply afd_eqb_eq in Hf; rename Hf into Hfd end.
match goal with Ht : Bool.eqb _ _ = true |- _ => apply eqb_prop in Ht; rename Ht into Htid end.
match goal with Hh : list_eqb hop_eqb (a_hna cs) _ = true |- _ => apply (list_eqb_eq hop_eqb hop_eqb_eq) in Hh; rename Hh into Hhna end.
match goal with Hh : list_eqb hop_eqb (a_hlz cs) _ = true |- _ => apply (list_eqb_eq hop_eqb hop_eqb_eq) in Hh; rename Hh into Hhlz end.
match goal with Hk : kn_incl_h _ _ (kn T) = true |- _ => rename Hk into Hkn end.
repeat match goal with Hz : Z.leb _ _ = true |- _ => apply Z.leb_le in Hz end.
set (E' := henv lo hi E (s_regs (a_ss cs)) (s_regs (a_ss T))).
exists E'. split; [apply henv_agree|]. split; [intros; apply henv_high; assumption|]. split; [|symmetry; exact Hpc].
set (Tc := set_regs T (s_regs (a_ss cs))).
assert (Evis : a_vis Tc = a_vis cs) by (unfold Tc; cbn [set_regs with_ss a_vis]; symmetry; exact Hallow).
assert (HA : allowA E Tc = allowA E cs) by (unfold allowA; unfold Tc; cbn [set_regs with_ss a_vis a_ghost]; rewrite Hallow, Hghost; reflexivity).
assert (HH : hid E Tc model = hid E cs model) by (apply hid_ext; exact Evis).
assert (HC1 : cs_ok E Tc R FULL model).
{ destruct HC; constructor; rewrite ?HA;
try (unfold Tc; cbn [set_regs with_ss a_ss mk_ss s_regs s_log s_know kn a_maps a_totsz a_ylo a_eager a_vis a_ghost a_abytes a_brk a_fd a_tidset a_hna a_hlz];
rewrite <- ?Hmaps, <- ?Hallow, <- ?Hghost, <- ?Hbrk, <- ?Hfd, <- ?Htid, <- ?Hhna, <- ?Hhlz; first [assumption | reflexivity | lia]).
- unfold Mr. rewrite HH. eapply kn_incl_h_sound; [exact co_know0 | exact Hkn].
- unfold Tc. cbn [set_regs with_ss a_maps a_ylo]. rewrite <- Hmaps. eapply holes_mono; [exact co_holes0 | lia].
- intros a. rewrite HH. replace (in_ghost E Tc) with (in_ghost E cs) by (unfold in_ghost, Tc; cbn [set_regs with_ss a_ghost]; rewrite Hghost; reflexivity).
exact (co_zero0 a). }
assert (ET : T = set_regs Tc (s_regs (a_ss T))).
{ subst Tc. clear - HL HRV. destruct T as [[p sr lg k nx rv] m t y e v g ab br f ti hna hlz]. cbn in HL, HRV. subst lg rv. reflexivity. }
rewrite ET at 1. eapply (cs_ok_reenv lo); try eassumption.
- apply henv_agree.
- unfold pairs_vars_lt, Tc. cbn [set_regs with_ss a_vis a_ghost]. rewrite forallb_app. apply andb_true_intro; split; assumption.
- apply regs_match_h_sound; [exact Hregs | exact Hlen | exact (co_regs _ _ _ _ _ HC)].
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_diamond_join_sound := (ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "R@'='Q3'<%113'S6'H'@%113&V9v0v^<r6r5r4r3r2%877654321(4r1%22?1%?3=41'G'Y=&R8y5'_2yR0%211%5241y8%511%I11p051'QL'X4r8%25G1FEB'I&Z9%13MLEr=%331NG%E231%95I8ONM&VL%11:r:%311%Q;3Q?31%L261%M281qR>M1%?2N1p0A1pl4E1pRFG1pTNL1pR<Q31r7%I5Q>1Q=Q<Q9r9%A11%QI3QMA1%Q:2D1%Q;2F1qR>Q;1%M2Q<1p081pl4Q31pRFQ51pTNQ:1pR<QA1%QC2?1p0QE1pi:R61phFR71phDR81pm>R:1pjNR=1plHR?1")) (only parsing).
Variable nx : ltac:(sec_ty2 constr:(SEC_T_diamond_join_sound) 0%nat 0%nat).
Variable joinpc : ltac:(sec_ty2 constr:(SEC_T_diamond_join_sound) 1%nat 0%nat).
Variable rs : ltac:(sec_ty2 constr:(SEC_T_diamond_join_sound) 2%nat 0%nat).
Variable ca : ltac:(sec_ty2 constr:(SEC_T_diamond_join_sound) 3%nat 0%nat).
Variable cb : ltac:(sec_ty2 constr:(SEC_T_diamond_join_sound) 4%nat 0%nat).
Variable csj : ltac:(sec_ty2 constr:(SEC_T_diamond_join_sound) 5%nat 0%nat).
Lemma diamond_join_sound : ltac:(sec_stmt2 constr:(SEC_T_diamond_join_sound) 6%nat 0%nat).
Proof using SEGS_in_hull HULL_ok e_sp0_init argH_agree SINV_agree nx joinpc rs ca cb csj.
intros H.
unfold node_diamond_join in H.
match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
injection H as <-.
repeat match type of Hc with (_ && _)%bool = true => apply andb_prop in Hc as [Hc ?X] end.
match goal with Hl : Nat.eqb (length ?l) 32 = true |- _ => apply Nat.eqb_eq in Hl; rename Hl into Hlen end.
match goal with Hl : Nat.leb nx0 ?v = true |- _ => apply Nat.leb_le in Hl; rename Hl into Hn0 end.
split; intros E R FULL model HC.
- match goal with Hea : entails_h A ?lo ?hi ca ?T = true |- _ =>
destruct (entails_h_sound lo hi E ca T R FULL model HC Hea Hn0 Hlen) as (E' & Hag & _ & HC' & Hpc) end.
exists E'. split; [split; eapply env_agree_le; [exact Hag | lia | exact Hag | lia] | split; [exact HC' | exact Hpc]].
- match goal with Hea : entails_h A ?lo ?hi cb ?T = true |- _ =>
destruct (entails_h_sound lo hi E cb T R FULL model HC Hea Hn0 Hlen) as (E' & Hag & _ & HC' & Hpc) end.
exists E'. split; [split; eapply env_agree_le; [exact Hag | lia | exact Hag | lia] | split; [exact HC' | exact Hpc]].
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_loop_ok_facts := (ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "R9'S6'='Y@'Q3'H'@%113&UHv^<r5r4r3r2%6554321(4r1%22=1%=3;41'G'7&T9r6%22>1(D%D3521'N&VI%116%321C&O%41C%22F1'<'YM%211&YJ&S4%11J%311(?%117%Q53731&;&YK%117%32Q;1uQ0%Q;3Q>21&T3%12FQ7%Q>3O1K&Z2&U7%11Q0%321Q<%Q92QDQ;%QD3QB21&[4&Z1%22Q?1%Q:241%Q;2;1%Q<2?1%Q=2F1%Q>2Q11%Q?2Q51%Q@2Q:1p0QB1plDR11pjFR51pTJR41pS6R61phNR81")) (only parsing).
Variable cs : ltac:(sec_ty2 constr:(SEC_T_loop_ok_facts) 0%nat 0%nat).
Variable J : ltac:(sec_ty2 constr:(SEC_T_loop_ok_facts) 1%nat 0%nat).
Variable N : ltac:(sec_ty2 constr:(SEC_T_loop_ok_facts) 2%nat 0%nat).
Variable inv : ltac:(sec_ty2 constr:(SEC_T_loop_ok_facts) 3%nat 0%nat).
Variable nhi : ltac:(sec_ty2 constr:(SEC_T_loop_ok_facts) 4%nat 0%nat).
Lemma loop_ok_facts : ltac:(sec_stmt2 constr:(SEC_T_loop_ok_facts) 5%nat 0%nat).
Proof using Type cs J N inv nhi.
intros H.
unfold loop_ok in H.
match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
destruct (xhi (kn cs) N) as [h|] eqn:Hx; [|discriminate]. destruct (Z.ltb h two64) eqn:Hlt; [|discriminate]. injection H as <-.
apply Z.ltb_lt in Hlt.
repeat match type of Hc with (_ && _)%bool = true => apply andb_prop in Hc as [Hc ?X] end.
apply Nat.leb_le in X12. apply Nat.ltb_lt in X11.
destruct (s_log (a_ss inv)); [|discriminate]. apply Nat.eqb_eq in X7.
repeat split; try assumption; reflexivity.
Qed.
End SE.
#[using="Type"] Lemma pc_inst : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "A'S6'='Y@'H'Q3&VL&TIr3r2r1%43321%611%715%:3921pi@<1pS6>1pjF@1").
Proof. reflexivity. Qed.
#[using="Type"] Lemma nxt_inst : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "@'S6'='Y@'H&VI&TIr3r2r1%43321%611%715%93;21pi@;1pS6=1pjF?1").
Proof. reflexivity. Qed.
Section SE.
Local Abbreviation SEC_T_check_all_ok := (ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "Q='S6'VM'SCp021p041'<%116'W<'H&S@v0r4r3r2%544321(RLr1%211%:3@41'G'I&ZK%13F6;r6r5%2291%;1>%C3I21'F%:221%;281qi2O1%<2Q01r7%12E;%D1H%L3Q221p0?1phNQ61%D271p0F1pm@Q21pi<Q41pk0Q:1phJQ81")) (only parsing).
Variable chk : ltac:(sec_ty2 constr:(SEC_T_check_all_ok) 0%nat 0%nat).
Variable k : ltac:(sec_ty2 constr:(SEC_T_check_all_ok) 1%nat 0%nat).
Lemma check_all_ok : ltac:(sec_stmt2 constr:(SEC_T_check_all_ok) 2%nat 0%nat).
Proof using Type chk k.
intros css s H.
unfold check_all in H. destruct css as [|cs0 rest]; [discriminate|].
destruct (chk cs0 k) as [s0|] eqn:H0; [|discriminate].
match type of H with fold_left ?F rest (COk s0) = _ =>
assert (GEN : forall l acc, fold_left F l acc = COk s ->
acc = COk s /\ forall cs, In cs l -> chk cs k = COk s) end.
{ induction l as [|c l IHl]; intros acc Hf; cbn [fold_left] in Hf.
- split; [exact Hf | intros ? []].
- destruct acc as [s1|c1 q1 r1].
+ destruct (chk c k) as [s'|] eqn:Hc'; [| apply IHl in Hf as [Hf _]; discriminate].
destruct (shape_eqb s1 s') eqn:Hse; [| apply IHl in Hf as [Hf _]; discriminate].
apply IHl in Hf as [E1 Hl]. injection E1 as ->. apply shape_eqb_eq in Hse. subst s'.
split; [reflexivity|]. intros cs [<-|Hin]; [exact Hc' | apply Hl; exact Hin].
+ apply IHl in Hf as [Hf _]. discriminate. }
apply GEN in H as [E0 Hrest]. injection E0 as ->.
split; [exists cs0; split; [left; reflexivity | split; [exact H0 | exact I]]|].
intros cs [<-|Hin]; [exact H0 | apply Hrest; exact Hin].
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_check_vars := (ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "Q:'='@'UI%211'VM'S6'W<'H'SC&S?vZJvQAv0v^<vQEv[Ev[Dv[CvQ@vQDr6r5r4r2r3%@??>=<;:987654321(RLr1%211%F3E41'7&W>%12C9(D%K3421p061pm@N1phNQ01pm8Q21pkDQ41pj0Q81pgNQ91")) (only parsing).
Variable bfuel : ltac:(sec_ty2 constr:(SEC_T_check_vars) 0%nat 0%nat).
Lemma check_vars : ltac:(sec_stmt2 constr:(SEC_T_check_vars) 1%nat 0%nat).
Proof using Type bfuel.
intros fuel.
induction fuel as [|fuel IH]; intros lc p cs s Hc; [discriminate|].
cbn [APK.check] in Hc.
match type of Hc with (if ?g then _ else _) = _ => destruct g; [discriminate|] end.
destruct p as [stops k|e mid k1 k2|ce cmid ck1 ck2|db1 db2 dk1 dk2|sb1 sn1 sb2 sn2 k| |K k|jb joff jn k|ixs k|db dn k|gws k|bm k|hrs k|hbK k|r logc fb k|y k|ma mb|ia ib ic|qa qb|ka kb|x args k|xid xargs k|eid eargs k|bid bargs kb1 kb2|lJ lN linv lbody lk| |h| | |fi fsz fk|gi gsz gk|gb gn gk2|ub un uk|hlo hhi hk|ilo ihi ik|djp drs dk|rnm rnk|cpk|vj vjs vlo vka vk|mj|ab an ak|hws hwk|rsr rse rsk|iha ihb ihc|hai halo hahi hanl hanh hak|wb woff wn wlo whi wk|lha lhb].
- destruct (run_block_gc SEGS IT _ KC bfuel (stops ++ STOPS A) cs) as [cs1|]; [|discriminate]. exact (IH _ k cs1 s Hc).
- destruct (APK.expr_vars_lt nx0 e) eqn:Hv; [|discriminate].
destruct (erange (kn cs) e) as [[lo hi]|]; [|discriminate].
destruct (Z.leb lo mid && Z.ltb mid hi)%bool.
2: { destruct (Z.leb hi mid); [exact (IH _ k1 _ s Hc) | exact (IH _ k2 _ s Hc)]. }
destruct (CHECK bfuel fuel lc (set_kn cs (KRange e lo mid :: kn cs)) k1) as [s1|] eqn:H1; [|discriminate].
destruct (CHECK bfuel fuel lc (set_kn cs (KRange e (mid+1) hi :: kn cs)) k2) as [s2|] eqn:H2; [|discriminate].
injection Hc as <-. cbn [shape_vars_lt]. rewrite Hv, (IH _ k1 _ s1 H1), (IH _ k2 _ s2 H2). reflexivity.
- destruct (erange (kn cs) ce) as [[lo hi]|]; [|discriminate].
destruct (Z.leb lo cmid && Z.ltb cmid hi)%bool.
2: { cbn [negb] in Hc. destruct (Z.leb hi cmid); [exact (IH _ ck1 _ s Hc) | exact (IH _ ck2 _ s Hc)]. }
cbn [negb] in Hc. cbv zeta in Hc.
destruct (kn_contra (kn (set_kn cs (KRange ce lo cmid :: kn cs)))); [exact (IH _ ck2 _ s Hc)|].
destruct (kn_contra (kn (set_kn cs (KRange ce (cmid + 1) hi :: kn cs)))); [exact (IH _ ck1 _ s Hc)|].
destruct (CHECK bfuel fuel lc (set_kn cs (KRange ce lo cmid :: kn cs)) ck1) as [s1|] eqn:H1; [|discriminate].
destruct (CHECK bfuel fuel lc (set_kn cs (KRange ce (cmid+1) hi :: kn cs)) ck2) as [s2|] eqn:H2; [|discriminate].
destruct (shape_eqb s1 s2); [|discriminate]. injection Hc as <-. exact (IH _ ck1 _ s1 H1).
- destruct (node_casedisj cs db1 db2) as [[csa csb]|]; [|discriminate].
destruct (CHECK bfuel fuel lc csa dk1) as [s1|] eqn:H1; [|discriminate].
destruct (CHECK bfuel fuel lc csb dk2) as [s2|] eqn:H2; [|discriminate].
destruct (shape_eqb s1 s2); [|discriminate]. injection Hc as <-. exact (IH _ dk1 _ s1 H1).
- destruct (node_shdisj A cs sb1 sn1 sb2 sn2) as [cs1|]; [|discriminate]. exact (IH _ k cs1 s Hc).
- destruct (kn_contra (kn cs)); [|discriminate]. injection Hc as <-. reflexivity.
- destruct (fact_ok (kn cs) K); [|discriminate]. exact (IH _ k _ s Hc).
- destruct (node_join SEGS cs jb joff jn) as [cs1|]; [|discriminate]. exact (IH _ k cs1 s Hc).
- exact (IH _ k _ s Hc).
- exact (IH _ k _ s Hc).
- exact (IH _ k _ s Hc).
- destruct (node_bump cs bm) as [cs1|]; [|discriminate]. exact (IH _ k cs1 s Hc).
- destruct (node_havoc nx0 cs hrs) as [cs1|]; [|discriminate]. exact (IH _ k cs1 s Hc).
- destruct (node_havocbig nx0 cs hbK) as [cs1|]; [|discriminate]. exact (IH _ k cs1 s Hc).
- destruct (node_fresh nx0 cs r logc fb) as [cs1|]; [|discriminate]. exact (IH _ k cs1 s Hc).
- destruct (is_ecall_at SEGS cs); [|discriminate]. destruct (node_sys A nx0 y cs) as [cs1|]; [|discriminate]. exact (IH _ k cs1 s Hc).
- destruct (is_ecall_at SEGS cs); [|discriminate]. destruct (node_mmap2 A nx0 LIMIT false cs) as [[csa csb]|]; [|discriminate].
exact (IH _ mb _ s Hc).
- destruct (is_ecall_at SEGS cs); [|discriminate]. destruct (node_mmapin A LIMIT false cs) as [[[csa csb] cscs]|]; [|discriminate].
exact (IH _ ib _ s Hc).
- destruct (is_ecall_at SEGS cs); [|discriminate]. destruct (node_mprotect2 A LIMIT cs) as [[csa csb]|]; [|discriminate].
exact (IH _ qb _ s Hc).
- destruct (is_ecall_at SEGS cs); [|discriminate]. destruct (node_brk2 A LIMIT cs) as [[csa csb]|]; [|discriminate].
destruct (CHECK bfuel fuel lc csa ka) as [sa|] eqn:H1; [|discriminate].
destruct (CHECK bfuel fuel lc csb kb) as [sb|] eqn:H2; [|discriminate].
destruct (hole_only sa && hole_only sb)%bool; [|discriminate].
injection Hc as <-. apply salt2_vars; [exact (IH _ ka _ sa H1) | exact (IH _ kb _ sb H2)].
- destruct (node_x SEGS A nx0 x args cs) as [cs1|]; [|discriminate]. exact (IH _ k cs1 s Hc).
- destruct (XN xid xargs cs) as [cs1|]; [|discriminate]. exact (IH _ k cs1 s Hc).
- destruct (XE eid eargs cs) as [[[fd ps] cs1]|]; [|discriminate].
destruct (CHECK bfuel fuel lc cs1 k) as [s1|] eqn:H1; [|discriminate].
injection Hc as <-. cbn [shape_vars_lt]. exact (IH _ k cs1 s1 H1).
- destruct (XB bid bargs cs) as [[csa csb]|]; [|discriminate].
destruct (CHECK bfuel fuel lc csa kb1) as [sa|] eqn:H1; [|discriminate].
destruct (CHECK bfuel fuel lc csb kb2) as [sb|] eqn:H2; [|discriminate].
injection Hc as <-. cbn [shape_vars_lt]. rewrite (IH _ kb1 _ sa H1), (IH _ kb2 _ sb H2). reflexivity.
- destruct (loop_ok nx0 cs lJ lN linv) as [nhi|]; [|discriminate].
destruct (Z.eqb (pc linv) (pc cs) && entails_h A (Datatypes.S lJ) (nxt linv) cs (inst linv lJ (ELit 0)))%bool; [|discriminate].
destruct (CHECK bfuel fuel (Some (LC (pc cs) (inst linv lJ (eaddz (EVar lJ) 1)) (Datatypes.S lJ) (nxt linv))) (loop_body_state lJ lN nhi linv) lbody) as [sb|]; [|discriminate].
destruct sb; try discriminate. exact (IH _ lk _ s Hc).
- destruct lc as [[h nx lo hi|j' js' sk' b' lo']|]; [|discriminate|discriminate].
destruct (Z.eqb (pc cs) h && entails_h A lo hi cs nx)%bool; [|discriminate]. injection Hc as <-. reflexivity.
- destruct (HS h) as [ch|]; [|discriminate]. destruct (entails cs ch); [|discriminate]. injection Hc as <-. reflexivity.
- destruct (is_ecall_at SEGS cs); [|discriminate]. destruct (node_exit cs); [|discriminate]. injection Hc as <-. reflexivity.
- discriminate Hc.
- destruct (node_fog cs fi fsz) as [cs1|]; [|discriminate]. exact (IH _ fk cs1 s Hc).
- destruct (node_fognew cs gi gsz) as [cs1|]; [|discriminate]. exact (IH _ gk cs1 s Hc).
- destruct (node_ghost LIMIT cs gb gn) as [cs1|]; [|discriminate]. exact (IH _ gk2 cs1 s Hc).
- destruct (node_unvis A cs ub un) as [cs1|]; [|discriminate]. exact (IH _ uk cs1 s Hc).
- destruct (node_havocbrk nx0 cs hlo hhi) as [cs1|]; [|discriminate]. exact (IH _ hk cs1 s Hc).
- destruct (node_intro nx0 cs ilo ihi) as [cs1|]; [|discriminate]. exact (IH _ ik cs1 s Hc).
- destruct (branch_probe IT cs) as [e|]; [|discriminate].
destruct (erange (kn cs) e) as [[lo hi]|]; [|discriminate].
destruct (Z.ltb hi 1 || Z.ltb 0 lo)%bool.
{ destruct (run_block_gc SEGS IT _ KC bfuel (djp :: STOPS A) cs) as [cs1|]; [|discriminate].
destruct (Z.eqb (pc cs1) djp); [|discriminate]. exact (IH _ dk cs1 s Hc). }
cbv zeta in Hc.
destruct (run_block_gc SEGS IT _ KC bfuel (djp :: STOPS A) (set_kn cs (KRange e lo 0 :: kn cs))) as [ca|]; [|discriminate].
destruct (run_block_gc SEGS IT _ KC bfuel (djp :: STOPS A) (set_kn cs (KRange e 1 hi :: kn cs))) as [cb|]; [|discriminate].
destruct (node_diamond_join A nx0 (nxt cs) djp drs ca cb) as [csj|]; [|discriminate]. exact (IH _ dk csj s Hc).
- destruct (node_rename _ cs rnm) as [cs1|]; [|discriminate]. exact (IH _ rnk cs1 s Hc).
- destruct (node_compact _ cs) as [cs1|]; [|discriminate]. exact (IH _ cpk cs1 s Hc).
- destruct (via_ok nx0 cs vjs vlo); [|discriminate].
destruct (CHECK bfuel fuel lc vjs vk) as [sk|]; [|discriminate]. exact (IH _ vka _ s Hc).
- destruct lc as [[h nx lo hi|j' js' sk' b' lo']|]; [discriminate| |discriminate].
destruct (Nat.eqb mj j' && Z.eqb (pc cs) (pc js') && shape_vars_lt nx0 sk' && entails_h A lo' (nxt js') cs js')%bool eqn:Ht; [|discriminate].
injection Hc as <-. apply andb_prop in Ht as [Ht _]. apply andb_prop in Ht as [_ Hsv]. exact Hsv.
- destruct (node_abstractcell A cs ab an) as [cs1|]; [|discriminate]. exact (IH _ ak cs1 s Hc).
- destruct (node_havocwords nx0 cs hws) as [cs1|]; [|discriminate]. exact (IH _ hwk cs1 s Hc).
- destruct (node_respell cs rsr rse) as [cs1|]; [|discriminate]. exact (IH _ rsk cs1 s Hc).
-
destruct (is_ecall_at SEGS cs); [|discriminate]. destruct (node_mmapin A LIMIT true cs) as [[[csa csb] cscs]|]; [|discriminate].
exact (IH _ ihb _ s Hc).
- destruct (node_habs nx0 cs hai halo hahi hanl hanh) as [cs1|]; [|discriminate]. exact (IH _ hak cs1 s Hc).
- destruct (node_absword nx0 cs wb woff wn wlo whi) as [cs1|]; [|discriminate]. exact (IH _ wk cs1 s Hc).
-
destruct (is_ecall_at SEGS cs); [|discriminate]. destruct (node_mmap2 A nx0 LIMIT true cs) as [[csa csb]|]; [|discriminate].
destruct (kn_contra (kn csa)); [exact (IH _ lhb _ s Hc)|].
destruct (kn_contra (kn csb)); [exact (IH _ lha _ s Hc)|].
destruct (CHECK bfuel fuel lc csa lha) as [sa|] eqn:H1; [|discriminate].
destruct (CHECK bfuel fuel lc csb lhb) as [sb|] eqn:H2; [|discriminate].
destruct (shape_eqb sa sb); [|discriminate]. injection Hc as <-. exact (IH _ lha _ sa H1).
Qed.
End SE.
#[using="Type"] Lemma list_set_nth_maps_match : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "R3'Y='<'S<%211'B'_2yR0%211%4211%811'='Q3'H'@%11<&[0r5r3%33@21(4r2%22C1%:3841'7&TJ%118(9%?3421'G&[3z%221>&[4&Z1%22A1%7241&_3&Y<r9&S;%11H%4231%62Q41r4%?221&XDr:r8%332:1r;&UF&T8r6%211%44QD718%:361Ap081p0=1p0G1p0Q01p0Q61pn>QB1pkJQL1pjBQE1pk<QG1pl8QN1pR<R21").
Proof.
intros E ms. induction ms as [|m0 ms IH]; intros l i m sz Hn Hf Hsz Hle HM; [destruct i; discriminate|].
destruct i as [|i]; cbn [nth_error] in Hn; cbn [list_set_nth maps_match] in *.
- injection Hn as ->. rewrite Hf in HM. destruct HM as (l' & -> & HM).
unfold fog_token, is_fog. cbn [am_kind am_len mkind_eqb]. right. exists (amap_den E m), l'.
split; [reflexivity|]. split; [|exact HM]. unfold uE, amap_den. cbn [snd edenot]. rewrite u64_lit by (unfold two64 in Hsz; lia). exact Hle.
- destruct (is_fog m0).
+ destruct HM as [HM|(iv & l' & -> & Hs & HM)]; [left; eapply IH; eassumption | right].
exists iv, l'. split; [reflexivity|]. split; [exact Hs | eapply IH; eassumption].
+ destruct HM as (l' & -> & HM). exists l'. split; [reflexivity | eapply IH; eassumption].
Qed.
#[using="Type"] Lemma list_insert_nth_maps_match : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "N'Y='<'S<%211'B'_2yR0%211%4211%811'='Q3&XDr5r4r3%43321r6&UE&T8r2%211%44D719%;3619p081pn>>1pjB@1pk<B1pl8I1pR<M1").
Proof.
intros E ms. induction ms as [|m0 ms IH]; intros l i sz HM.
- destruct i; cbn [list_insert_nth maps_match]; unfold fog_token, is_fog; cbn [am_kind mkind_eqb]; left; exact HM.
- destruct i as [|i]; cbn [list_insert_nth].
+ cbn [maps_match]. unfold fog_token at 1. unfold is_fog at 1. cbn [am_kind mkind_eqb]. left. exact HM.
+ cbn [maps_match] in *. destruct (is_fog m0).
* destruct HM as [HM|(iv & l' & -> & Hs & HM)]; [left; apply IH; exact HM | right].
exists iv, l'. split; [reflexivity|]. split; [exact Hs | apply IH; exact HM].
* destruct HM as (l' & -> & HM). exists l'. split; [reflexivity | apply IH; exact HM].
Qed.
#[using="Type"] Lemma In_list_set_nth : forall {T} (l : list T) i x y, In y (list_set_nth i x l) -> y = x \/ In y l.
Proof.
intros T l. induction l as [|a l IH]; intros i x y H; [destruct i; cbn in H; destruct H|].
destruct i; cbn in H; destruct H as [H|H]; try (right; left; exact H); try (left; symmetry; exact H).
- right. right. exact H.
- destruct (IH _ _ _ H) as [->|H']; [left; reflexivity | right; right; exact H'].
Qed.
#[using="Type"] Lemma In_list_insert_nth : forall {T} (l : list T) i x y, In y (list_insert_nth i x l) -> y = x \/ In y l.
Proof.
intros T l. induction l as [|a l IH]; intros i x y H.
- destruct i; cbn in H; destruct H as [H|[]]; left; symmetry; exact H.
- destruct i; cbn in H; destruct H as [H|H]; try (left; symmetry; exact H); try (right; left; exact H).
+ right. exact H.
+ destruct (IH _ _ _ H) as [->|H']; [left; reflexivity | right; right; exact H'].
Qed.
#[using="Type"] Lemma cs_ok_with_maps : forall E cs R FULL model ms',
cs_ok E cs R FULL model ->
maps_match E ms' (vm_maps (m_vmmaps model)) ->
(forall m, In m ms' -> m = fog_token (match am_len m with ELit z => z | _ => 0 end) \/ In m (a_maps cs)) ->
cs_ok E (with_maps cs ms') R FULL model.
Proof.
intros E cs R FULL model ms' HC HM Hsub.
assert (HMr : Mr E (with_maps cs ms') model FULL = Mr E cs model FULL) by reflexivity.
assert (HA : allowA E (with_maps cs ms') = allowA E cs) by reflexivity.
destruct HC; constructor; unfold with_maps; rewrite ?HMr, ?HA;
cbn [a_ss a_maps a_totsz a_ylo a_eager a_vis a_ghost a_abytes a_brk a_fd a_tidset a_hna a_hlz kn] in *; try assumption.
- apply Forall_forall. intros m Hin Hk. destruct (Hsub m Hin) as [Hm|Hm].
+ rewrite Hm in Hk. cbn in Hk. discriminate.
+ exact (proj1 (Forall_forall _ _) co_holes0 m Hm Hk).
- apply Forall_forall. intros m Hin Hk. destruct (Hsub m Hin) as [Hm|Hm].
+ rewrite Hm in Hk. cbn in Hk. destruct Hk; discriminate.
+ exact (proj1 (Forall_forall _ _) co_none0 m Hm Hk).
- apply Forall_forall. intros m Hin Hk. destruct (Hsub m Hin) as [Hm|Hm].
+ rewrite Hm in Hk. cbn in Hk. discriminate.
+ exact (proj1 (Forall_forall _ _) co_kinds0 m Hm Hk).
Qed.
#[using="Type"] Lemma fog_sound : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "QC'Y='S6&R8y5'_2yR0%211%5241'@y8%611%311p061'QL'='Q3'X4r8r7r6r5r4%6554321'H%@1G&V;r3%23:61(4r2%22M1%83741'Gr:%B518A@?&VL%11:r9%311%@3H31%8261p0:1p0D1pi0Q:1pn>M1pjBO1pl4Q11pRFQ31pTNQ91phNQ@1pR<QB1").
Proof.
intros E cs R FULL model i sz cs' HC H. unfold node_fog in H.
destruct (nth_error (a_maps cs) i) as [m|] eqn:Hn; [|discriminate].
match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
injection H as <-. split; [|reflexivity].
apply andb_prop in Hc as [Hc Hx]. apply andb_prop in Hc as [Hc Hs2]. apply andb_prop in Hc as [Hnf Hs1].
apply negb_true_iff in Hnf. apply Z.leb_le in Hs1. apply Z.ltb_lt in Hs2.
destruct (xhi (kn cs) (am_len m)) as [h|] eqn:Hh; [|discriminate]. apply Z.leb_le in Hx.
pose proof (xhi_sound SEGS E _ (kn cs) (am_len m) h (co_know _ _ _ _ _ HC) Hh) as Hh'.
apply cs_ok_with_maps; [exact HC | |].
- eapply list_set_nth_maps_match; [exact Hn | exact Hnf | lia | lia | exact (co_maps _ _ _ _ _ HC)].
- intros m' Hin. destruct (In_list_set_nth _ _ _ _ Hin) as [->|Hin']; [left; reflexivity | right; exact Hin'].
Qed.
#[using="Type"] Lemma fognew_sound : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "QC'Y='S6&R8y5'_2yR0%211%5241'@y8%611%311p061'QL'='Q3'X4r8r7r6r5r4%6554321'H%@1G&V<r3%23:61(4r2%22M1%83741'Gr:%B518A@?&VL%11:r9%311%@3H31%8261p0:1p0D1pi0Q:1pn>M1pjBO1pl4Q11pRFQ31pTNQ91phNQ@1pR<QB1").
Proof.
intros E cs R FULL model i sz cs' HC H. unfold node_fognew in H.
match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
injection H as <-. split; [|reflexivity].
apply cs_ok_with_maps; [exact HC | apply list_insert_nth_maps_match; exact (co_maps _ _ _ _ _ HC) |].
intros m' Hin. destruct (In_list_insert_nth _ _ _ _ Hin) as [->|Hin']; [left; reflexivity | right; exact Hin'].
Qed.
#[using="Type"] Lemma page_allowedb_app_l : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "J'<'B'Q3%2211%411'_2yR0%211'H'7&RHr3r1%3221(D%73621&6r4%23?17r2%:221%=3<17p071pm8@1pkBD1pk@E1").
Proof. intros. unfold page_allowedb in *. rewrite existsb_app, H. reflexivity. Qed.
#[using="Type"] Lemma MInv_app_r : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "Q2'<'B'Q3%2211%411'QL'RCr3r1%3221&[3&[1&RDr2%211&R@&6r4%23?1;%411%9261&R4&R0%11:%311%?251r5%;3H1:%F21Ep041p0E1pkJJ1pkBL1pk@M1").
Proof.
intros l1 l2 m [N1 N2 N3 N4 N5] Hb. constructor; try assumption.
intros p Hp. apply page_allowedb_app_l. apply N3. exact Hp.
Qed.
#[using="HS XN XE XB SHADOW_ok KC"] Lemma allow1_cost : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "M'Y='Y@'Q3&[3&_3yR0&Y<r4r2%3221%6251r1%9221&R@&X1r5(Ar3%24AA;1%5241%711&WD%11>%D231p0<1plDG1pl:I1pgFJ1pR<L1").
Proof.
intros E b n nhi Hn. unfold allow1, vis_cost. cbn [A_bytes fst snd]. unfold sh_lo, sh_hi. cbn [fst snd].
pose proof (u64_range (edenot E b)) as Rb. pose proof (u64_range (edenot E n)) as Rn. unfold uE in *. pose proof SHADOW_ok as So. unfold shadow_ok in So.
pose proof (pageup_pagedown_gap (bv_unsigned (edenot E b)) (bv_unsigned (edenot E b) + bv_unsigned (edenot E n)) ltac:(lia)) as G1.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
pose proof (pageup_pagedown_gap (shadow_off A + bv_unsigned (edenot E b) / 8)
(shadow_off A + (bv_unsigned (edenot E b) + bv_unsigned (edenot E n)) / 8) ltac:(lia)) as G2.
assert (G3 : (bv_unsigned (edenot E b) + bv_unsigned (edenot E n)) / 8 - bv_unsigned (edenot E b) / 8 <= nhi / 8 + 1) by lia.
lia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.
#[using="HS XN XE XB SHADOW_ok KC"] Lemma ghost_sound : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "QD'Y='S6&R8y5'_2yR0%211%5241'@y8%611%311p061'QL'Y@'X4r8r7r6r5r4%6554321'H%?1F&V=vQEr3%342;71(4r2%22M1%93841'Gr:%C518BA@'Q3&VL%11;r9%311%B3531%9271p0;1p0F1pi0Q;1pl:O1pgFQ01pl4Q21pRFQ41pTNQ:1phNQA1pR<QC1").
Proof.
intros E cs R FULL model b n cs' HC H. unfold node_ghost in H.
destruct (xhi (kn cs) n) as [nhi|] eqn:Hx; [|discriminate].
match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
injection H as <-. split; [|reflexivity].
apply andb_prop in Hc as [Hc Hb]. apply Z.leb_le in Hb.
pose proof (xhi_sound SEGS E _ (kn cs) n nhi (co_know _ _ _ _ _ HC) Hx) as Hn.
set (cs' := ACS _ _ _ _ _ _ _ _ _ _ _ _ _).
assert (HMr : Mr E cs' model FULL = Mr E cs model FULL) by reflexivity.
assert (HA : allowA E cs' = allowA E cs ++ allow1 E (b, n)).
{ unfold allowA, cs'. cbn [a_vis a_ghost]. rewrite app_assoc, !flat_map_app. cbn [flat_map]. rewrite app_nil_r. reflexivity. }
assert (HAB : A_bytes (allowA E cs') <= A_bytes (allowA E cs) + vis_cost nhi).
{ rewrite HA, A_bytes_app. pose proof (allow1_cost E b n nhi Hn). lia. }
pose proof (co_limit _ _ _ _ _ HC) as HL. pose proof (co_eager _ _ _ _ _ HC) as HE. pose proof (co_abytes _ _ _ _ _ HC) as HAB0.
destruct HC; constructor; unfold cs'; rewrite ?HMr;
cbn [a_ss a_maps a_totsz a_ylo a_eager a_vis a_ghost a_abytes a_brk a_fd a_tidset a_hna a_hlz kn] in *; try assumption.
- fold cs'. lia.
- fold cs'. rewrite HA. apply MInv_app_r; [exact co_minv0|]. rewrite <- HA. fold cs' in HAB. rewrite HL. lia.
- intros a H1 H2 H3 H4 H5. apply (co_zero0 a H1 H2 H3 H4).
unfold in_ghost in H5 |- *. cbn [a_ghost] in H5. rewrite existsb_app in H5. apply orb_false_iff in H5 as [H5 _]. exact H5.
Qed.
Section SE.
Local Abbreviation SEC_T_kzero_x_sound0 := (ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "RA'Y='_2yR0%211'@y8%511%311p051'<'YE%211'Y@'Q3&Z6vZJr7r6r5%544321r8%746153'H'7&UCr4r3%35;:921(D%73621'G&[3zr1%3221&[4&Z3r;%221D%4261%:261&_1&[1&Z4r<(Y8%12JN%4231r2%7221%92Q@1%>11(4%<2Q@E%22Q@1%Q13Q@41p0@1pjBQ<1r:%>2Q:Q9%A221%N2M1%J24Q5%E231&[9+2+R0%3221%Q5251%Q7281%Q82=1p0Q:1p0QC1p0QF1pl:QN1pm6QN1pgFR01pk0R21pgDR31pTDR71pR<R@1")) (only parsing).
Variable E : ltac:(sec_ty2 constr:(SEC_T_kzero_x_sound0) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_kzero_x_sound0) 1%nat 0%nat).
Variable allkn : ltac:(sec_ty2 constr:(SEC_T_kzero_x_sound0) 2%nat 0%nat).
Lemma kzero_x_sound0 : ltac:(sec_stmt2 constr:(SEC_T_kzero_x_sound0) 3%nat 0%nat).
Proof using Type E M allkn.
intros k b off n Hall HK H.
induction k as [|K rest IH]; [discriminate|].
apply Forall_cons_iff in HK as [HKK Hrest].
destruct K; try exact (IH Hrest H).
lazymatch type of H with context [KZero ?za ?zl :: rest] => destruct za as [zb zk]; rename zl into zn end.
cbn [kzero_x] in H.
assert (H2w : forall c1 c2 : bool, (if c1 then true else if c2 then true else kzero_x allkn rest b off n) = true ->
(c1 || c2)%bool = true \/ kzero_x allkn rest b off n = true)
by (intros [|] [|]; cbn; auto).
apply H2w in H. destruct H as [H|H]; [|exact (IH Hrest H)].
cbn [kentry_ok] in HKK. destruct HKK as [Hfl Hz]. pose proof Hfl as Hfl'. destruct Hfl' as (F1 & F2 & F3 & F4).
unfold estart in Hz, F1, F2, F4 |- *. cbn [a_base a_off] in Hz, F1, F2, F4 |- *.
pose proof (u64_range (edenot E n)) as Hnr.
assert (CORE : bv_unsigned (edenot E zb) + zk <= bv_unsigned (edenot E b) + off ->
bv_unsigned (edenot E b) + off + elenZ E n <= bv_unsigned (edenot E zb) + zk + elenZ E zn ->
(forall i, 0 <= i < elenZ E n -> M (Z_to_bv 64 (bv_unsigned (edenot E b) + off + i)) = Some (Z_to_bv 8 0))
/\ 0 <= bv_unsigned (edenot E b) + off /\ bv_unsigned (edenot E b) + off + elenZ E n <= 2 ^ 64).
{ intros A0 B0. split; [|unfold elenZ in *; lia]. intros i Hi.
replace (bv_unsigned (edenot E b) + off + i) with (bv_unsigned (edenot E zb) + zk + (bv_unsigned (edenot E b) + off - (bv_unsigned (edenot E zb) + zk) + i)) by lia.
apply Hz. lia. }
apply orb_prop in H as [H|H].
- destruct (expr_eqb b zb && Z.leb zk off)%bool eqn:H01; [|discriminate]. apply andb_prop in H01 as [H0 H1].
apply expr_eqb_eq in H0. apply Z.leb_le in H1. subst zb.
destruct (xhi allkn n) as [nh|] eqn:Hxh; [|discriminate].
destruct (xlo allkn zn) as [zl|] eqn:Hxl; [|discriminate]. apply Z.leb_le in H.
pose proof (xhi_sound SEGS E M allkn n nh Hall Hxh). pose proof (xlo_sound SEGS E M allkn zn zl Hall Hxl).
apply CORE; unfold elenZ in *; lia.
- pose proof (xinside_sound SEGS E M allkn b off n zb zk zn Hall H) as [A0 B0].
unfold estart in A0, B0. cbn [a_base a_off] in A0, B0. apply CORE; lia.
Qed.
End SE.
#[using="Type"] Lemma A_bytes_fm_split : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "Q5'Y='B'Y@%2211'7p021'<%114'H'Q3&R@&ZN%;233&X1r3%211r1%64>521%811&[1&ZMr2%23C16%<4D;81%>11&>%<1:%211qm8I1%93J1=%C4KB?1%E11%=281%I3H?1pk<K1piJN1pR<Q41").
Proof.
intros E f l. induction l as [|p l IH]; cbn [flat_map List.filter]; [reflexivity|].
rewrite A_bytes_app, IH. destruct (f p); cbn [negb flat_map]; rewrite ?A_bytes_app; lia.
Qed.
#[using="Type"] Lemma A_bytes_allow1_nonneg : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "?'Y='B'Y@%2211&[3z&R@&X1r2r1%3221%511%8271pm8:1pR<>1").
Proof.
intros E p. unfold allow1. cbn [A_bytes fst snd].
pose proof (pagedown_le (uE E (fst p))). pose proof (pageup_ge (uE E (fst p) + uE E (snd p))).
pose proof (pagedown_le (sh_lo E p)). pose proof (pageup_ge (sh_hi E p)).
pose proof (u64_range (edenot E (snd p))). unfold sh_lo, sh_hi, uE in *.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
lia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.
#[using="Type"] Lemma vis_here_eq : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "D'Y@'B%1222'H'7&WEr3r2r1%43321(D%83721(Ar4%24>>18%<3=81p051pm8?1pl:B1pgFC1").
Proof.
intros b n [pb pn] H. unfold vis_here in H. cbn [fst snd] in H. apply andb_prop in H as [H1 H2].
apply expr_eqb_eq in H1. apply expr_eqb_eq in H2. subst. reflexivity.
Qed.
#[using="Type"] Lemma A_bytes_fm_here : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "Q8'Y='Y@'<'B%1233%311'Q0'Hr1(Ar4r3%34;;21%63951qm8:1%93;17'Q3&R@&ZN%@233&X1r5%211r2%64D521%811&[6&[7&;%12I6%311%;2:C%?11%7231%K3B91p0D1pk<O1pl:Q41pgFQ51pR<Q71").
Proof.
intros E b n l H. induction l as [|p l IH]; [reflexivity|].
apply Forall_cons_iff in H as [-> H]. cbn [flat_map length]. rewrite A_bytes_app, (IH H). rewrite Nat2Z.inj_succ. lia.
Qed.
#[using="SHADOW_ok"] Lemma unvis_sound : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "QD'Y='S6&R8y5'_2yR0%211%5241'@y8%611%311p061'QL'Y@'X4r8r7r6r5r4%6554321'H%?1F&VGv0r3%342;71(4r2%22M1%93841'Gr:%C518BA@'Q3&VL%11;r9%311%B3531%9271p0;1p0F1pi0Q;1pl:O1pgFQ01pl4Q21pRFQ41pTNQ:1phNQA1pR<QC1").
Proof.
intros E cs R FULL model b n cs' HC H. rewrite node_unvis_eq in H. unfold node_unvis_ref in H.
destruct (split_lit b) as [bb bk] eqn:Hsp.
destruct (shadow_of A (kn cs) b n) as [[sb sk] sn] eqn:Hsh.
destruct (xhi (kn cs) b) as [bh|] eqn:Hbh; [|discriminate].
destruct (xhi (kn cs) n) as [nh|] eqn:Hnh; [|discriminate].
match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
match type of H with Some ?x = Some _ => assert (Hcs : cs' = x) by congruence end. subst cs'. clear H.
split; [|reflexivity].
repeat match type of Hc with (_ && _)%bool = true => apply andb_prop in Hc as [Hc ?X] end.
rename Hc into Hex.
match goal with Hl : Z.leb 3 (ealign (kn cs) b) = true |- _ => apply Z.leb_le in Hl; rename Hl into Hab end.
match goal with Hl : Z.leb 3 (ealign (kn cs) n) = true |- _ => apply Z.leb_le in Hl; rename Hl into Han end.
match goal with Hl : flat_x (kn cs) bb bk n = true |- _ => rename Hl into Hfl end.
match goal with Hl : Z.leb (bh + nh) CEIL = true |- _ => apply Z.leb_le in Hl; rename Hl into Hceil end.
match goal with Hl : flat_x (kn cs) sb sk sn = true |- _ => rename Hl into Hfls end.
match goal with Hl : kzero_x (kn cs) (kn cs) sb sk sn = true |- _ => rename Hl into Hkz end.
pose proof (co_know _ _ _ _ _ HC) as HK.
set (M := Mr E cs model FULL) in *.
pose proof (xhi_sound SEGS E M (kn cs) b bh HK Hbh) as Hbh'. pose proof (xhi_sound SEGS E M (kn cs) n nh HK Hnh) as Hnh'.
pose proof (flat_x_sound E M (kn cs) bb bk n HK Hfl) as (F1 & F2 & F3).
pose proof (split_lit_denot E b bb bk Hsp) as Hbd.
set (ub := bv_unsigned (edenot E b)) in *. set (un := bv_unsigned (edenot E n)) in *.
assert (HB : estart E (SA bb bk) = ub).
{ unfold ub. rewrite Hbd. unfold estart. cbn [a_base a_off]. rewrite u64_lit; [reflexivity|]. unfold estart in F1, F2; cbn [a_base a_off] in F1, F2. lia. }
rewrite HB in *.
pose proof (shadow_of_val E M (kn cs) b n sb sk sn HK Hsh Hfls) as [HS0 HSn]. fold ub in HS0. fold un in HSn.
pose proof SHADOW_ok as So; unfold shadow_ok in So. pose proof (u64_range (edenot E b)) as Rb. fold ub in Rb.
assert (HSS : estart E (SA sb sk) = shadow_off A + ub / 8).
{ rewrite HS0. rewrite Z.mod_small; [lia|]. unfold CEIL in Hceil.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
set (S := shadow_off A + ub / 8) in *.
pose proof (ealign_sound SEGS E M (kn cs) b HK) as [Hrb0 Hdb]. pose proof (ealign_sound SEGS E M (kn cs) n HK) as [Hrn0 Hdn].
fold ub in Hdb. fold un in Hdn.
assert (D8b : (8 | ub)). { eapply Z.divide_trans; [|exact Hdb]. exists (2 ^ (ealign (kn cs) b - 3)). change 8 with (2 ^ 3). rewrite <- Z.pow_add_r by lia. f_equal. lia. }
assert (D8n : (8 | un)). { eapply Z.divide_trans; [|exact Hdn]. exists (2 ^ (ealign (kn cs) n - 3)). change 8 with (2 ^ 3). rewrite <- Z.pow_add_r by lia. f_equal. lia. }
assert (Hshhi : shadow_off A + (ub + un) / 8 = S + un / 8).
{ unfold S. destruct D8b as [qb ->]. destruct D8n as [qn ->].
rewrite Z.div_mul, <- Z.mul_add_distr_r, !Z.div_mul by lia. lia. }
pose proof (kzero_x_sound0 E M (kn cs) (kn cs) sb sk sn HK HK Hkz) as (Hzero & _ & _). rewrite HSS, HSn in Hzero.
assert (GONE : Forall (fun p => p = (b, n)) (List.filter (vis_here b n) (a_vis cs))).
{ apply Forall_forall. intros p Hp. apply filter_In in Hp as [_ Hp]. apply vis_here_eq. exact Hp. }
set (cs' := ACS _ _ _ _ _ _ _ _ _ _ _ _ _).
assert (ALLOW_sub : forall z, in_allow E cs' z = true -> in_allow E cs z = true).
{ intros z Hz. unfold in_allow, in_vis, in_sh in *. unfold cs' in Hz; cbn [a_vis] in Hz.
apply orb_true_iff in Hz. apply orb_true_iff.
destruct Hz as [Hz|Hz]; [left|right]; apply existsb_exists in Hz as [q [Hq Hzq]]; apply filter_In in Hq as [Hq _];
apply existsb_exists; exists q; split; assumption. }
assert (ALLOW_eq : forall z, ~ (ub <= z < ub + un) -> ~ (S <= z < S + un / 8) -> in_allow E cs' z = in_allow E cs z).
{ intros z Hz1 Hz2. destruct (in_allow E cs' z) eqn:Ha'; [symmetry; apply ALLOW_sub; exact Ha'|].
destruct (in_allow E cs z) eqn:Ha; [|reflexivity]. exfalso.
unfold in_allow, in_vis, in_sh in Ha, Ha'. unfold cs' in Ha'; cbn [a_vis] in Ha'.
apply orb_false_iff in Ha' as [Hv' Hs'].
assert (Q : forall q, In q (a_vis cs) -> vis_here b n q = false ->
In q (List.filter (fun p => negb (vis_here b n p)) (a_vis cs))).
{ intros q Hq Hh. apply filter_In. split; [exact Hq | rewrite Hh; reflexivity]. }
apply orb_true_iff in Ha. destruct Ha as [Ha|Ha]; apply existsb_exists in Ha as [q [Hq Hzq]].
- destruct (vis_here b n q) eqn:Hh.
+ apply vis_here_eq in Hh. subst q. cbn [fst snd] in Hzq. apply andb_prop in Hzq as [Z1 Z2].
apply Z.leb_le in Z1. apply Z.ltb_lt in Z2. apply Hz1. unfold ub, un. unfold uE in Z1, Z2. lia.
+ assert (X : existsb (fun p => (uE E (fst p) <=? z) && (z <? uE E (fst p) + uE E (snd p)))%bool
(List.filter (fun p => negb (vis_here b n p)) (a_vis cs)) = true).
{ apply existsb_exists. exists q. split; [apply Q; assumption | exact Hzq]. }
rewrite X in Hv'. discriminate.
- destruct (vis_here b n q) eqn:Hh.
+ apply vis_here_eq in Hh. subst q. apply andb_prop in Hzq as [Z1 Z2].
apply Z.leb_le in Z1. apply Z.ltb_lt in Z2. unfold sh_lo, sh_hi in Z1, Z2. cbn [fst snd] in Z1, Z2.
apply Hz2. unfold S. unfold ub, un in *. unfold uE in Z1, Z2. rewrite Hshhi in Z2. unfold S in Z2. lia.
+ assert (X : existsb (fun p => (sh_lo E p <=? z) && (z <? sh_hi E p))%bool
(List.filter (fun p => negb (vis_here b n p)) (a_vis cs)) = true).
{ apply existsb_exists. exists q. split; [apply Q; assumption | exact Hzq]. }
rewrite X in Hs'. discriminate. }
assert (HID_mono : forall a, hid E cs model a = true -> hid E cs' model a = true).
{ intros a Ha. unfold hid in *. apply orb_true_iff in Ha. apply orb_true_iff. destruct Ha as [Ha|Ha]; [left; exact Ha|right].
apply negb_true_iff in Ha. apply negb_true_iff. destruct (vis E cs' model a) eqn:Hv; [|reflexivity].
rewrite (vis_mono E cs' cs model a ALLOW_sub Hv) in Ha. discriminate. }
assert (HID_eq : forall a, ~ (ub <= bv_unsigned a < ub + un) -> ~ (S <= bv_unsigned a < S + un / 8) ->
hid E cs' model a = hid E cs model a).
{ intros a H1 H2. unfold hid, vis. change (a_maps cs') with (a_maps cs). rewrite (ALLOW_eq _ H1 H2). reflexivity. }
set (M' := Mr E cs' model FULL).
assert (M_none : forall x, M x = None -> M' x = None).
{ intros x Hx. unfold M, M', Mr, mrestrict in *. destruct (hid E cs model x) eqn:Hh.
- rewrite (HID_mono x Hh). reflexivity.
- destruct (hid E cs' model x); [reflexivity | exact Hx]. }
assert (M_eq : forall x, ~ (ub <= bv_unsigned x < ub + un) -> ~ (S <= bv_unsigned x < S + un / 8) -> M' x = M x).
{ intros x H1 H2. unfold M, M', Mr, mrestrict. rewrite (HID_eq x H1 H2). reflexivity. }
set (k1 := kn_unfill (kn cs) bb bk n).
set (Mmid := fun x : word => if ((ub <=? bv_unsigned x) && (bv_unsigned x <? ub + un))%bool then M' x else M x).
assert (Mmid_out : forall x : word, bv_unsigned x < ub \/ ub + elenZ E n <= bv_unsigned x -> Mmid x = M x).
{ intros x Hx. unfold Mmid. unfold elenZ in Hx. fold un in Hx.
destruct ((ub <=? bv_unsigned x) && (bv_unsigned x <? ub + un))%bool eqn:Hb; [|reflexivity].
apply andb_prop in Hb as [Z1 Z2]. apply Z.leb_le in Z1. apply Z.ltb_lt in Z2. lia. }
assert (IMG : forall lo hi Mx, (forall x, M x = None -> Mx x = None) ->
kentry_ok SEGS E M (KImg lo hi) -> kentry_ok SEGS E Mx (KImg lo hi)).
{ intros lo hi Mx Hn HKi. cbn [kentry_ok] in *. destruct HKi as (I1 & I2 & I3). split; [exact I1|]. split; [exact I2|].
intros i Hi. apply Hn. apply I3. exact Hi. }
assert (Mmid_none : forall x, M x = None -> Mmid x = None).
{ intros x Hx. unfold Mmid. destruct (_ && _)%bool; [apply M_none; exact Hx | exact Hx]. }
assert (HK1 : know_ok SEGS E Mmid k1).
{ unfold k1, kn_unfill. cbv zeta. apply Forall_forall. intros K HinK. apply filter_In in HinK as [HinK Hkeep].
pose proof (proj1 (Forall_forall _ _) HK K HinK) as HKK.
apply orb_prop in Hkeep as [Himg|Hap].
- destruct K; try discriminate. apply (IMG _ _ Mmid Mmid_none HKK).
- rewrite kentry_apart_bp_eq in Hap. eapply kentry_apart_keep; [exact HK | exact HKK | exact Hap |]. rewrite HB. exact Mmid_out. }
assert (HK2 : know_ok SEGS E M' (kn_unfill k1 sb sk sn)).
{ unfold kn_unfill. cbv zeta. apply Forall_forall. intros K HinK. apply filter_In in HinK as [HinK Hkeep].
pose proof (proj1 (Forall_forall _ _) HK1 K HinK) as HKK.
assert (HinK0 : In K (kn cs)) by (unfold k1, kn_unfill in HinK; apply filter_In in HinK as [HinK _]; exact HinK).
apply orb_prop in Hkeep as [Himg|Hap].
- destruct K; try discriminate. apply (IMG _ _ M' M_none). exact (proj1 (Forall_forall _ _) HK _ HinK0).
- rewrite kentry_apart_bp_eq in Hap. eapply kentry_apart_keep; [exact HK1 | exact HKK | exact Hap |].
rewrite HSS, HSn. intros x Hx. unfold Mmid.
destruct ((ub <=? bv_unsigned x) && (bv_unsigned x <? ub + un))%bool eqn:Hb; [reflexivity|].
apply M_eq; [|lia]. intros Hin. assert (X : ((ub <=? bv_unsigned x) && (bv_unsigned x <? ub + un))%bool = true); [|rewrite X in Hb; discriminate].
apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
assert (HA : allowA E cs' = flat_map (allow1 E) (List.filter (fun p => negb (vis_here b n p)) (a_vis cs))
++ flat_map (allow1 E) (a_ghost cs) ++ allow1 E (b, n)).
{ unfold allowA, cs'. cbn [a_vis a_ghost]. rewrite !flat_map_app. cbn [flat_map]. rewrite app_nil_r, app_assoc. reflexivity. }
assert (HA0 : allowA E cs = flat_map (allow1 E) (a_vis cs) ++ flat_map (allow1 E) (a_ghost cs)).
{ unfold allowA. rewrite flat_map_app. reflexivity. }
assert (HAB : A_bytes (allowA E cs') <= A_bytes (allowA E cs)).
{ rewrite HA, HA0, !A_bytes_app.
rewrite (A_bytes_fm_split E (fun p => negb (vis_here b n p)) (a_vis cs)).
assert (FF : List.filter (fun p => negb (negb (vis_here b n p))) (a_vis cs) = List.filter (vis_here b n) (a_vis cs)).
{ apply filter_ext. intros q. apply negb_involutive. }
rewrite FF, (A_bytes_fm_here E b n _ GONE).
assert (L1 : (1 <= length (List.filter (vis_here b n) (a_vis cs)))%nat).
{ apply existsb_exists in Hex as [q [Hq Hh]].
assert (Hin : In q (List.filter (vis_here b n) (a_vis cs))) by (apply filter_In; split; assumption).
destruct (List.filter (vis_here b n) (a_vis cs)); [destruct Hin | cbn; lia]. }
pose proof (A_bytes_allow1_nonneg E (b, n)). nia. }
assert (HPG : forall pg, page_allowedb (allowA E cs) pg = true -> page_allowedb (allowA E cs') pg = true).
{ intros pg Hp. unfold page_allowedb in *. apply existsb_exists in Hp as [iv [Hiv Hpg]]. apply existsb_exists.
exists iv. split; [|exact Hpg]. rewrite HA. rewrite HA0 in Hiv. rewrite !in_app_iff in *.
destruct Hiv as [Hiv|Hiv]; [|right; left; exact Hiv].
apply in_flat_map in Hiv as [q [Hq Hiv]]. destruct (vis_here b n q) eqn:Hh.
- apply vis_here_eq in Hh. subst q. right; right. exact Hiv.
- left. apply in_flat_map. exists q. split; [|exact Hiv]. apply filter_In. split; [exact Hq | rewrite Hh; reflexivity]. }
pose proof (co_minv _ _ _ _ _ HC) as HMI. pose proof (co_abytes _ _ _ _ _ HC) as HAB0. pose proof (co_zero _ _ _ _ _ HC) as HZ0.
destruct HC; constructor; unfold cs'; cbn [a_ss a_maps a_totsz a_ylo a_eager a_vis a_ghost a_abytes a_brk a_fd a_tidset a_hna a_hlz kn s_regs s_log s_know mk_ss]; try assumption; try reflexivity.
all: fold cs'.
all: match goal with
| |- know_ok _ _ _ _ => change (Mr E cs' model FULL) with M'; exact HK2
| |- A_bytes _ <= _ => lia
| |- MInv _ _ => destruct HMI as [N1 N2 N3 N4 N5]; constructor; try assumption; [intros pg Hpg; apply HPG; apply N3; exact Hpg | lia]
| |- _ => idtac
end.
intros a H1 H2 H3 H4 H5.
unfold in_ghost in H5. unfold cs' in H5; cbn [a_ghost] in H5. rewrite existsb_app in H5. apply orb_false_iff in H5 as [H5 H6].
cbn [existsb fst snd] in H6. rewrite orb_false_r in H6.
assert (NA : ~ (ub <= bv_unsigned a < ub + un)).
{ intros Hin. assert (X : ((uE E b <=? bv_unsigned a) && (bv_unsigned a <? uE E b + uE E n))%bool = true); [|rewrite X in H6; discriminate].
unfold uE. fold ub un. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
destruct (hid E cs model a) eqn:Hh.
+ apply (HZ0 a Hh H2 H3 H4). unfold in_ghost. exact H5.
+ destruct (Z_le_dec S (bv_unsigned a)) as [L1|L1]; [destruct (Z_lt_dec (bv_unsigned a) (S + un / 8)) as [L2|L2]|].
*
pose proof (Hzero (bv_unsigned a - S) ltac:(lia)) as Z0.
replace (S + (bv_unsigned a - S)) with (bv_unsigned a) in Z0 by lia. rewrite Z_to_bv_bv_unsigned in Z0.
unfold M, Mr, mrestrict in Z0. rewrite Hh in Z0. exact Z0.
* rewrite (HID_eq a NA ltac:(lia)) in H1. rewrite Hh in H1. discriminate.
* rewrite (HID_eq a NA ltac:(lia)) in H1. rewrite Hh in H1. discriminate.
Qed.
#[using="e_sp0_init argH_agree SINV_agree"] Lemma havocbrk_sound : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "QO'Y='S6&R8y5'_2yR0%211%5241'@y8%611%311p061'QL'Q3'X4r8r7r6r5r4%6554321'H%?1F&VAv^<r3%342;71(4r2%22M1%93841'I'G&Z9r;r1%33<21&VIr:%211%73165%9251r9%M58H1LK&VL%11J%218%J3Q221%@251%A281qR>QC1%D2QD1p0F1p0Q11pi0QF1pj<Q:1pkHQ;1pl4Q=1pRFQ?1pTNQE1phNQL1pR<QN1").
Proof.
intros E cs R FULL model lo hi cs' HC H. unfold node_havocbrk in H.
destruct (xlo (kn cs) (a_brk cs)) as [l|] eqn:Hl; [|discriminate].
destruct (xhi (kn cs) (a_brk cs)) as [h|] eqn:Hh; [|discriminate].
match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
injection H as <-.
apply andb_prop in Hc as [Hc H2]. apply andb_prop in Hc as [Hf H1]. apply Z.leb_le in H1. apply Z.leb_le in H2.
pose proof (xlo_sound SEGS E _ (kn cs) (a_brk cs) l (co_know _ _ _ _ _ HC) Hl) as L1.
pose proof (xhi_sound SEGS E _ (kn cs) (a_brk cs) h (co_know _ _ _ _ _ HC) Hh) as L2.
destruct (fresh_ok_parts cs Hf) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
set (v := nxt cs). set (E' := ext1 E v (vm_brk (m_vmmaps model))).
assert (Hag : env_agree v E E') by apply ext1_agree.
pose proof (cs_ok_agree E E' cs R FULL model Hag Hf HC) as HC'.
exists E'. split; [split; [eapply env_agree_le; [exact Hag | exact Fle] | exact Hag]|]. split; [|reflexivity].
assert (Hv : edenot E' (EVar v) = vm_brk (m_vmmaps model)) by (cbn [edenot]; unfold E'; apply ext1_at).
pose proof (co_brk _ _ _ _ _ HC) as HB0.
set (cs' := ACS _ _ _ _ _ _ _ _ _ _ _ _ _).
assert (HMr : Mr E' cs' model FULL = Mr E' cs model FULL) by reflexivity.
assert (HA : allowA E' cs' = allowA E' cs) by reflexivity.
destruct HC'; constructor; unfold cs'; rewrite ?HMr, ?HA;
cbn [a_ss a_maps a_totsz a_ylo a_eager a_vis a_ghost a_abytes a_brk a_fd a_tidset a_hna a_hlz kn mk_ss s_regs s_log s_know s_pc s_next] in *;
try assumption; try reflexivity.
- constructor; [|exact co_know0]. cbn [kentry_ok]. rewrite Hv, HB0. lia.
- symmetry. exact Hv.
Qed.
#[using="e_sp0_init argH_agree SINV_agree"] Lemma intro_sound : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "QO'Y='S6&R8y5'_2yR0%211%5241'@y8%611%311p061'QL'Q3'X4r8r7r6r5r4%6554321'H%?1F&VCv^<r3%342;71(4r2%22M1%93841'I'G&Z9r;r1%33<21&VIr:%211%73165%9251r9%M58H1LK&VL%11J%218%J3Q221%@251%A281qR>QC1%D2QD1p0F1p0Q11pi0QF1pj<Q:1pkHQ;1pl4Q=1pRFQ?1pTNQE1phNQL1pR<QN1").
Proof.
intros E cs R FULL model lo hi cs' HC H. unfold node_intro in H.
match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
injection H as <-.
apply andb_prop in Hc as [Hc H3]. apply andb_prop in Hc as [Hc H2]. apply andb_prop in Hc as [Hf H1].
apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.ltb_lt in H3.
destruct (fresh_ok_parts cs Hf) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
set (v := nxt cs). set (E' := ext1 E v (Z_to_bv 64 lo)).
assert (Hag : env_agree v E E') by apply ext1_agree.
pose proof (cs_ok_agree E E' cs R FULL model Hag Hf HC) as HC'.
exists E'. split; [split; [eapply env_agree_le; [exact Hag | exact Fle] | exact Hag]|]. split; [|reflexivity].
assert (Hv : bv_unsigned (edenot E' (EVar v)) = lo).
{ cbn [edenot]. unfold E'. rewrite ext1_at. unfold two64 in H3. apply u_small. lia. }
set (cs' := with_ss _ _).
assert (HMr : Mr E' cs' model FULL = Mr E' cs model FULL) by reflexivity.
assert (HA : allowA E' cs' = allowA E' cs) by reflexivity.
destruct HC'; constructor; unfold cs'; rewrite ?HMr, ?HA;
cbn [with_ss a_ss a_maps a_totsz a_ylo a_eager a_vis a_ghost a_abytes a_brk a_fd a_tidset a_hna a_hlz kn mk_ss s_regs s_log s_know s_pc s_next] in *;
try assumption; try reflexivity.
- constructor; [|exact co_know0]. cbn [kentry_ok]. rewrite Hv. lia.
Qed.
#[using="Type"] Lemma hop_sub_replay : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "Q9'Y='Y@'<'T?%211'H'_2yR0%211&Y<r6r3%3221r5%5241%:3731r7%8216%9225%>3;21'B%12==%D11&X<r8&Q1&TCr4%24<B?1%44JJ1B%7261%827D%K3:21p0>1p0C1pj8O1piHQ31piDQ41pl:Q51pgFQ61pR<Q81").
Proof.
intros E b n eb en h Hb Hn.
assert (G : forall y, edenot E (if expr_eqb y n then en else y) = edenot E y).
{ intros y. destruct (expr_eqb y n) eqn:E2; [apply expr_eqb_eq in E2; subst y; exact Hn| reflexivity]. }
induction h as [|[x y|x y] h IH]; [reflexivity| |]; cbn [map hop_sub];
(destruct (expr_eqb x b) eqn:E1; [apply expr_eqb_eq in E1; subst x|]); cbn [hreplay]; unfold uE; rewrite IH, ?Hb, ?G; reflexivity.
Qed.
Section SE.
Local Abbreviation SEC_T_habs_sound := (ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "R6'Y='S6&R8y5'_2yR0%211%5241'@y8%611%311p061'QL'='Q3'X4r;r:r9r8r7%6554321'H%@1G&V>v^<r6r5r4r3%675>:4321(4r2%22Q11%<3;41'I'G&Z9r>r1%33?21&VIr=%211%73165%9251r<%Q058C1ON&VL%11E%218%M3Q521%@251%A281qR>QG1%D2QH1p0F1p0Q41pi0QJ1plDQ=1plFQ>1pj<Q?1pkHQ@1pjBQB1pl4QD1pRFQF1pTNQL1phNR31pR<R51")) (only parsing).
Variable E : ltac:(sec_ty2 constr:(SEC_T_habs_sound) 0%nat 0%nat).
Variable cs : ltac:(sec_ty2 constr:(SEC_T_habs_sound) 1%nat 0%nat).
Variable R : ltac:(sec_ty2 constr:(SEC_T_habs_sound) 2%nat 0%nat).
Variable FULL : ltac:(sec_ty2 constr:(SEC_T_habs_sound) 3%nat 0%nat).
Variable model : ltac:(sec_ty2 constr:(SEC_T_habs_sound) 4%nat 0%nat).
Variable i : ltac:(sec_ty2 constr:(SEC_T_habs_sound) 5%nat 0%nat).
Variable lo : ltac:(sec_ty2 constr:(SEC_T_habs_sound) 6%nat 0%nat).
Variable hi : ltac:(sec_ty2 constr:(SEC_T_habs_sound) 7%nat 0%nat).
Variable nlo : ltac:(sec_ty2 constr:(SEC_T_habs_sound) 8%nat 0%nat).
Variable nhi : ltac:(sec_ty2 constr:(SEC_T_habs_sound) 9%nat 0%nat).
Variable cs' : ltac:(sec_ty2 constr:(SEC_T_habs_sound) 10%nat 0%nat).
Lemma habs_sound : ltac:(sec_stmt2 constr:(SEC_T_habs_sound) 11%nat 0%nat).
Proof using e_sp0_init argH_agree SINV_agree E cs R FULL model i lo hi nlo nhi cs'.
intros HC H.
unfold node_habs in H.
destruct (nth_error (a_hlz cs) i) as [hev|] eqn:Hnth; [|discriminate].
destruct (xlo (kn cs) (hop_b hev)) as [blo|] eqn:Hblo; [|discriminate].
destruct (xhi (kn cs) (hop_b hev)) as [bhi|] eqn:Hbhi; [|discriminate].
destruct (xhi (kn cs) (eadd (hop_b hev) (hop_n hev))) as [ehi|] eqn:Hehi; [|discriminate].
destruct (xlo (kn cs) (hop_n hev)) as [nl|] eqn:Hnl; [|discriminate].
destruct (xhi (kn cs) (hop_n hev)) as [nh|] eqn:Hnh; [|discriminate].
match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end. injection H as <-.
apply andb_prop in Hc as [Hc H6]. apply andb_prop in Hc as [Hc H5]. apply andb_prop in Hc as [Hc H4]. apply andb_prop in Hc as [Hc H3]. apply andb_prop in Hc as [Hc H3l].
apply andb_prop in Hc as [Hc H2b]. apply andb_prop in Hc as [Hc H2]. apply andb_prop in Hc as [Hf H1].
apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.leb_le in H2b. apply Z.leb_le in H3l. apply Z.leb_le in H3. apply Z.leb_le in H4. apply Z.ltb_lt in H5. apply Z.leb_le in H6.
set (b := hop_b hev) in *. set (n := hop_n hev) in *.
destruct (fresh_ok_parts cs Hf) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
pose proof (co_know _ _ _ _ _ HC) as HK.
pose proof (xlo_sound SEGS E _ (kn cs) b blo HK Hblo) as B1. pose proof (xhi_sound SEGS E _ (kn cs) b bhi HK Hbhi) as B1b.
pose proof (xhi_sound SEGS E _ (kn cs) (eadd b n) ehi HK Hehi) as B2.
pose proof (xlo_sound SEGS E _ (kn cs) n nl HK Hnl) as N1. pose proof (xhi_sound SEGS E _ (kn cs) n nh HK Hnh) as N2.
pose proof (ealign_sound SEGS E _ (kn cs) b HK) as [AB1 AB2]. pose proof (ealign_sound SEGS E _ (kn cs) n HK) as [AN1 AN2].
set (v := nxt cs). set (E1 := ext1 E v (edenot E b)). set (E' := ext1 E1 (Datatypes.S v) (edenot E n)).
assert (Hag1 : env_agree v E E1) by apply ext1_agree.
assert (Hag2 : env_agree (Datatypes.S v) E1 E') by apply ext1_agree.
assert (Hag : env_agree v E E') by (eapply env_agree_trans; [exact Hag1 | eapply env_agree_le; [exact Hag2 | lia]]).
pose proof (cs_ok_agree E E' cs R FULL model Hag Hf HC) as HC'.
exists E'. split; [split; [eapply env_agree_le; [exact Hag | exact Fle] | exact Hag]|]. split; [|reflexivity].
assert (Hvb : edenot E' (EVar v) = edenot E b).
{ cbn [edenot]. unfold E'. cbn [ext1 ev]. replace (Nat.eqb v (Datatypes.S v)) with false by (symmetry; apply Nat.eqb_neq; lia). apply ext1_at. }
assert (Hvn : edenot E' (EVar (Datatypes.S v)) = edenot E n) by (cbn [edenot]; unfold E'; apply ext1_at).
destruct (fresh_ok_hist cs Hf) as [Fhna Fhlz].
assert (Hev : In hev (a_hlz cs)) by (exact (nth_error_In _ _ Hnth)).
pose proof (proj1 (forallb_forall _ _) Fhlz hev Hev) as Hevv. apply andb_prop in Hevv as [Fb Fn]. fold b in Fb. fold n in Fn.
assert (Eb : edenot E' b = edenot E b) by (symmetry; eapply edenot_agree'; [exact Hag | exact Fb]).
assert (En : edenot E' n = edenot E n) by (symmetry; eapply edenot_agree'; [exact Hag | exact Fn]).
assert (Hsum : bv_unsigned (edenot E' (eadd (EVar v) (EVar (Datatypes.S v)))) = bv_unsigned (edenot E (eadd b n))).
{ unfold eadd. rewrite !mkAlu_denot. rewrite Hvb, Hvn. reflexivity. }
set (cs' := ACS _ _ _ _ _ _ _ _ _ _ _ _ _).
assert (HA : allowA E' cs' = allowA E' cs) by reflexivity.
destruct HC'; constructor; unfold cs'; rewrite ?HA;
cbn [a_ss a_maps a_totsz a_ylo a_eager a_vis a_ghost a_abytes a_brk a_fd a_tidset a_hna a_hlz kn mk_ss s_regs s_log s_know s_pc s_next] in *;
try assumption; try reflexivity.
-
match goal with |- know_ok _ _ (Mr ?EE ?c ?m ?F) _ => change (Mr EE c m F) with (Mr EE cs m F) end.
unfold know_ok. cbn [app]. constructor; [cbn [kentry_ok]; rewrite Hvb; lia|]. constructor; [cbn [kentry_ok]; rewrite Hvn; pose proof (u64_range (edenot E n)); lia|].
constructor; [cbn [kentry_ok]; rewrite Hsum; pose proof (u64_range (edenot E (eadd b n))); lia|].
rewrite !Forall_app. repeat split; [| | exact co_know0].
+ destruct (Z.leb_spec 12 (ealign (kn cs) b)); [|constructor]. constructor; [|constructor]. cbn [kentry_ok]. rewrite Hvb. split; [lia|].
apply Z.mod_divide; [lia|]. eapply Z.divide_trans; [|exact AB2]. exists (2 ^ (ealign (kn cs) b - 12)). change 4096 with (2 ^ 12). rewrite <- Z.pow_add_r by lia. f_equal. lia.
+ destruct (Z.leb_spec 12 (ealign (kn cs) n)); [|constructor]. constructor; [|constructor]. cbn [kentry_ok]. rewrite Hvn. split; [lia|].
apply Z.mod_divide; [lia|]. eapply Z.divide_trans; [|exact AN2]. exists (2 ^ (ealign (kn cs) n - 12)). change 4096 with (2 ^ 12). rewrite <- Z.pow_add_r by lia. f_equal. lia.
- unfold RNA in *. rewrite (hop_sub_replay E' b n) by (rewrite ?Hvb, ?Hvn, ?Eb, ?En; reflexivity). assumption.
- unfold RLZ in *. rewrite (hop_sub_replay E' b n) by (rewrite ?Hvb, ?Hvn, ?Eb, ?En; reflexivity). assumption.
Qed.
End SE.
#[using="Type"] Lemma kimg_cut_sound_aps : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "N'Y='_2yR0%211'@y8%511%311p051'<'YE%211'Q3&Z6vZJr5r4r3%544321r6&U6r2%23651%:49481p061pl:=1pg@>1pk0@1pTDD1pR<M1").
Proof.
intros E M k a n HK. unfold kimg_cut, know_ok. apply Forall_flat_map. apply Forall_forall. intros K Hin.
pose proof (proj1 (Forall_forall _ _) HK K Hin) as HKK.
unfold kimg_cut1. destruct K; try (apply Forall_one; exact HKK).
lazymatch goal with |- Forall _ (if _ then [KImg ?a ?b] else _) => rename a into lo; rename b into hi end.
destruct (Z.leb hi a || Z.leb (a + n) lo)%bool eqn:Hc; [apply Forall_one; exact HKK|].
apply orb_false_iff in Hc as [Hc1 Hc2]. apply Z.leb_gt in Hc1. apply Z.leb_gt in Hc2.
cbn [kentry_ok] in HKK. destruct HKK as (H0 & Hhi & Hnone).
apply Forall_app. split.
- destruct (Z.ltb lo a) eqn:Hl; [|constructor]. apply Z.ltb_lt in Hl. apply Forall_one. cbn [kentry_ok].
split; [lia|]. split; [lia|]. intros i Hi. apply Hnone. lia.
- destruct (Z.ltb (a + n) hi) eqn:Hh; [|constructor]. apply Z.ltb_lt in Hh. apply Forall_one. cbn [kentry_ok].
split; [lia|]. split; [lia|]. intros i Hi. apply Hnone. lia.
Qed.
#[using="Type"] Lemma kfind_litword_In : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "Q2'<'YE%211'Y@'Q3'='H'@%114&U3r5r4r3r2%544321(4r1%22=1%<3:41&ZK(Y6(Y8%12<;(Y2%11;%533=1r6%83J21p0:1ph:I1pl:I1pm6K1pgFM1pk0O1").
Proof.
induction k as [|K r IH]; intros b off n c H; [discriminate|]. cbn [kfind_litword] in H.
destruct K as [[b' off'] n' v| | | | | | | | |]; try (right; apply IH; exact H).
destruct v; try (right; apply IH; exact H).
destruct (expr_eqb b' b && (off' =? off) && Nat.eqb n' n)%bool eqn:E; [| right; apply IH; exact H].
injection H as <-. apply andb_prop in E as [E E3]. apply andb_prop in E as [E1 E2].
apply expr_eqb_eq in E1. apply Z.eqb_eq in E2. apply Nat.eqb_eq in E3. subst. left. reflexivity.
Qed.
#[using="e_sp0_init argH_agree SINV_agree"] Lemma absword_sound : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "R7'Y='S6&R8y5'_2yR0%211%5241'@y8%611%311p061'QL'Y@'Q3'='X4r;r:r9r8r7%6554321'H%A1H&V5v^<r6r5r4r3%675>:4321(4r2%22Q21%<3;41'I'G&Z9r>r1%33?21&VIr=%211%73165%9251r<%Q058C1ON&VL%11E%218%M3Q621%@251%A281qR>QH1%D2QI1p0F1p0Q41pi0QK1pj<Q>1pkHQ?1pl:Q?1pm6QA1pgFQC1pl4QE1pRFQG1pTNQM1phNR41pR<R61").
Proof.
intros E cs R FULL model b off n lo hi cs' HC H. unfold node_absword in H.
destruct (fresh_ok nx0 cs && Nat.leb 1 n && Nat.leb n 8)%bool eqn:Hc; [|discriminate].
destruct (kfind_litword (kn cs) b off n) as [c|] eqn:Hf; [|discriminate].
destruct (Z.leb lo c && Z.leb c hi && Z.leb 0 lo && Z.ltb hi two64)%bool eqn:Hr; [|discriminate].
injection H as <-.
apply andb_prop in Hc as [Hc Hn2]. apply andb_prop in Hc as [Hfr Hn1].
apply andb_prop in Hr as [Hr R4]. apply andb_prop in Hr as [Hr R3]. apply andb_prop in Hr as [R1 R2].
apply Z.leb_le in R1. apply Z.leb_le in R2. apply Z.leb_le in R3. apply Z.ltb_lt in R4. unfold two64 in R4.
destruct (fresh_ok_parts cs Hfr) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
set (v := nxt cs). set (E' := ext1 E v (Z_to_bv 64 c)).
assert (Hag : env_agree v E E') by apply ext1_agree.
pose proof (cs_ok_agree E E' cs R FULL model Hag Hfr HC) as HC'.
exists E'. split; [split; [eapply env_agree_le; [exact Hag | exact Fle] | exact Hag]|]. split; [|reflexivity].
match goal with |- cs_ok E' ?csx R FULL model =>
replace csx with (set_kn (bump cs 1) (KWord (SA b off) n (EVar v) :: KRange (EVar v) lo hi
:: kn_havoc (if expr_eqb b (ELit 0) then kimg_cut (kn cs) off (Z.of_nat n) else kn cs) b off (ELit (Z.of_nat n))))
by (unfold set_kn, bump, with_ss; cbn; rewrite Nat.add_1_r; reflexivity) end.
apply cs_ok_set_kn.
- destruct HC'; constructor; cbn [bump with_ss a_ss mk_ss s_regs s_log s_know kn a_maps a_totsz a_ylo a_eager a_vis a_abytes a_brk a_fd a_tidset a_hna a_hlz];
try assumption; reflexivity.
- pose proof (co_know _ _ _ _ _ HC') as HK'. change (Mr E' (bump cs 1) model FULL) with (Mr E' cs model FULL).
assert (Hv : edenot E' (EVar v) = Z_to_bv 64 c) by (cbn [edenot ev E' ext1]; rewrite Nat.eqb_refl; reflexivity).
constructor; [| constructor].
+ pose proof (proj1 (Forall_forall _ _) HK' _ (kfind_litword_In _ _ _ _ _ Hf)) as KW.
cbn [kentry_ok] in KW |- *. rewrite Hv. exact KW.
+ cbn [kentry_ok]. rewrite Hv, u64_lit by lia. lia.
+ eapply know_ok_havoc; [| intros; reflexivity| apply mem_grows_refl].
destruct (expr_eqb b (ELit 0)); [apply kimg_cut_sound_aps; exact HK'| exact HK'].
Qed.
Section Rename.
Variable m : list (nat * nat).
Variables fw bw : list (option nat).
Hypothesis Hfw : mk_fwd m = Some fw.
Hypothesis Hbw : mk_bwd m = Some bw.
#[using="Type"] Lemma mk_fwd_spec_gen : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "Q2'<'B'=%2211%411'@%114%711'H%412&ULr2%211(4r1%2281%83741&J&VHr4%2219%82C7%>3@21&ZK(A%14GG>;r5%43H21%;261pi>K1pm@L1p0?1pn@I1pkNM1").
Proof.
induction m0 as [|[s0 d0] rest IH]; intros t H s d; cbn [mk_fwd] in H.
- injection H as <-. unfold nt_get. cbn. split; [destruct s; discriminate | tauto].
- destruct (mk_fwd rest) as [t0|] eqn:E0; [|discriminate].
destruct (nt_get t0 s0) eqn:Eg; [discriminate|]. injection H as <-.
rewrite nt_get_set. specialize (IH t0 eq_refl).
destruct (Nat.eqb_spec s s0) as [->|NE].
+ split.
* intros X. injection X as <-. left. reflexivity.
* intros [X|X]; [congruence|]. apply IH in X. congruence.
+ rewrite IH. cbn. split; [tauto|]. intros [X|X]; [congruence|exact X].
Qed.
#[using="Type"] Lemma mk_bwd_spec_gen : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "Q2'<'B'=%2211%411'@%114%711'H%412&UKr2%211(4r1%2281%83741&J&VHr4%2216%82C:%>3@21&ZK(A%14GG>;r5%43H21%;261pi>K1pm@L1p0?1pn@I1pkNM1").
Proof.
induction m0 as [|[s0 d0] rest IH]; intros t H s d; cbn [mk_bwd] in H.
- injection H as <-. unfold nt_get. cbn. split; [destruct d; discriminate | tauto].
- destruct (mk_bwd rest) as [t0|] eqn:E0; [|discriminate].
destruct (nt_get t0 d0) eqn:Eg; [discriminate|]. injection H as <-.
rewrite nt_get_set. specialize (IH t0 eq_refl).
destruct (Nat.eqb_spec d d0) as [->|NE].
+ split.
* intros X. injection X as <-. left. reflexivity.
* intros [X|X]; [congruence|]. apply IH in X. congruence.
+ rewrite IH. cbn. split; [tauto|]. intros [X|X]; [congruence|exact X].
Qed.
#[using="Hfw"] Lemma fw_in : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "G'=&J'H'@%114&VHv]0r2%3221(4r1%22;1%:3841&ZK'B%12??(A%14AA:7v]L%63421%C281pi>E1pm@F1").
Proof. exact (mk_fwd_spec_gen m fw Hfw). Qed.
#[using="Hbw"] Lemma bw_in : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "G'=&J'H'@%114&VHv\2r1%3221(4r2%22;1%:3841&ZK'B%12??(A%14AA7:v]L%63421%C281pi>E1pm@F1").
Proof. exact (mk_bwd_spec_gen m bw Hbw). Qed.
Definition ren_env (E : env) : env :=
Env (fun w => match nt_get bw w with Some s => ev E s | None => ev E w end) (eb E).
Definition ren_ok (v : nat) : bool :=
match nt_get fw v with Some _ => true | None => match nt_get bw v with Some _ => false | None => true end end.
#[using="m Hfw Hbw"] Lemma edenot_rename : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "K'Y='Y@'H'7&T2&WOr1%3221(D%73621'_2yR0%211&Y<&WNr3%211&T0v]0r2%3221%8251%9273%E3;21p0?1pi@H1pR<J1").
Proof.
intros E e. induction e; cbn [evars_all erename edenot]; intros H;
try reflexivity;
try (apply andb_prop in H as [H1 H2]; rewrite (IHe1 H1), (IHe2 H2); reflexivity);
try (rewrite (IHe H); reflexivity).
unfold ren_ok in H. destruct (nt_get fw n) as [d|] eqn:Ef.
- cbn [edenot ren_env ev]. destruct (nt_get bw d) as [s|] eqn:Eb.
+ apply bw_in in Eb. apply fw_in in Ef. pose proof (proj2 (fw_in _ _) Eb) as Ef'.
assert (s = n) by (apply bw_in in Eb; apply bw_in in Ef; congruence). subst s. reflexivity.
+ exfalso. apply fw_in in Ef. apply (proj2 (bw_in _ _)) in Ef. congruence.
- cbn [edenot ren_env ev]. destruct (nt_get bw n) as [s|] eqn:Eb; [discriminate|reflexivity].
Qed.
End Rename.
Section RenameCS.
Variable m : list (nat * nat).
Variables fw bw : list (option nat).
Hypothesis Hfw : mk_fwd m = Some fw.
Hypothesis Hbw : mk_bwd m = Some bw.
Variable gb : nat.
Hypothesis Hgb : (nx0 <= gb)%nat.
Hypothesis Hm : forallb (fun p => Nat.leb gb (fst p) && Nat.leb gb (snd p)) m = true.
Let ER := edenot_rename m fw bw Hfw Hbw.
#[using="m Hbw Hm"] Lemma ren_agree : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "9'Y=&Z9v]1r1&XFv\2%2213%63541pR<81").
Proof.
intros E. split; [|reflexivity]. intros n Hn. cbn [ren_env ev].
destruct (nt_get bw n) as [s|] eqn:Eb; [|reflexivity].
apply (bw_in m bw Hbw) in Eb. exfalso.
pose proof (proj1 (forallb_forall _ _) Hm (s, n) Eb) as X. cbn [fst snd] in X.
apply andb_prop in X as [_ X]. apply Nat.leb_le in X. clear Hgb. lia.
Qed.
#[using="m Hfw Hbw ER"] Lemma uE_rename : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "K'Y='Y@'H'7&T2&XGv]0v\2%3221r1%6221(D%:3921'Q3&Y1&XFr3%22:1&T0r2%22>1%7241%8263%E3:21p0<1pi@H1pR<J1").
Proof. intros. unfold uE. rewrite (ER E e H). reflexivity. Qed.
#[using="m Hfw Hbw ER"] Lemma regs_ok_rename : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "Q8'Y='<'Y@%211&R8y5'_2yR0%211%5241'H'7&ZO&T2&XGv]0v\2%3221%511r2%83B21(D%<3;21&Z7r4r3%33217&XFr5%22=1&Q1&T0%11A%34OO19%;3519p091p0>1pTNL1pmLQ31pR<Q71").
Proof.
intros E sr R Hsr HR r. rewrite (HR r). unfold sr_get. destruct (bv_eqb r 0); [reflexivity|].
revert Hsr. generalize (ridx r) as i. clear HR r.
induction sr as [|e t IH]; intros i Hsr; [destruct i; reflexivity|].
cbn [forallb] in Hsr. apply andb_prop in Hsr as [He Ht].
destruct i as [|i]; cbn [map nth]; [symmetry; exact (ER E e He) | apply IH; exact Ht].
Qed.
#[using="Type"] Lemma eb_ren : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "B'Y='H'='<'_2y8%211%411p061&Y;&XFv\2r1%3221%511%613%?3821pR<A1").
Proof. reflexivity. Qed.
Section SE.
Local Abbreviation SEC_T_kentry_ok_rename := (ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "Q6'Y='_2yR0%211'@y8%511%311p051'YE'H'7&UA&XGv]0v\2%3221r1%6221(D%:3921&Z5vZJr4r3r2%544321&XFr5%22>1&U>%12A7%;4:391p071p0>1pS8J1pTDL1pR<Q51")) (only parsing).
Variable E : ltac:(sec_ty2 constr:(SEC_T_kentry_ok_rename) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_kentry_ok_rename) 1%nat 0%nat).
Lemma kentry_ok_rename : ltac:(sec_stmt2 constr:(SEC_T_kentry_ok_rename) 2%nat 0%nat).
Proof using m Hfw Hbw ER E M.
intros K HK Hk.
destruct K as [[ab ak] w v|[ab ak] n|[ab ak] n k|lo hi|ae am|re rlo rhi|[ab ak] wn|[b1 k1] dn1 [b2 k2] dn2|[ab ak] n fc|[ab ak] n];
unfold krename, arename in *; cbn [kvars_all kentry_ok a_base a_off] in *;
repeat match goal with H : (_ && _)%bool = true |- _ => apply andb_prop in H; destruct H as [? H] end;
unfold flat, estart, elenZ, adenot in *; cbn [a_base a_off] in *;
rewrite ?eb_ren; rewrite ?(ER E) by assumption; exact Hk.
Qed.
End SE.
#[using="m Hfw Hbw ER"] Lemma know_ok_rename : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "Q<'Y='_2yR0%211'@y8%511%311p051'<'YE%211'H'7&ZO&UA&XGv]0v\2%3221%511r1%83<21(D%<3;21&Z6vZJr4r3r2%544321&XFr5%22?1&Q1&U>%11C%34KK19%=4<5;1p091p0@1pk0N1pTDQ21pR<Q;1").
Proof.
intros E M k. induction k as [|K rest IH]; intros Hv Hk; [constructor|].
cbn [forallb] in Hv. apply andb_prop in Hv as [H1 H2]. apply Forall_cons_iff in Hk as [HK Hr].
cbn [map]. constructor; [apply kentry_ok_rename; assumption | apply IH; assumption].
Qed.
Definition pvars_all (l : list (expr * expr)) : bool :=
forallb (fun p => evars_all (ren_ok fw bw) (fst p) && evars_all (ren_ok fw bw) (snd p)) l.
#[using="m Hfw Hbw ER"] Lemma allowA_rename : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "Q7'Y='S6'='H'7&X0&S5r2%211%411(D%83721&S0r3%211%:11%=3<16'<'B'Q3%2211%411&X2&XFv\2r5%3221&W1v]0r4%3321A%9251%:273%N3<21p0B1p0H1plHQ21phNQ41pR<Q61").
Proof.
intros E cs nx Hv Hg. unfold allowA. cbn [rename_cs a_vis a_ghost]. rewrite <- map_app, !flat_map_concat_map, map_map. f_equal.
apply map_ext_in. intros p Hin.
assert (Hp : (evars_all (ren_ok fw bw) (fst p) && evars_all (ren_ok fw bw) (snd p))%bool = true).
{ apply in_app_iff in Hin as [Hin|Hin]; [exact (proj1 (forallb_forall _ _) Hv p Hin) | exact (proj1 (forallb_forall _ _) Hg p Hin)]. }
apply andb_prop in Hp as [H1 H2].
unfold allow1, sh_lo, sh_hi, prename. cbn [fst snd]. rewrite !(uE_rename E) by assumption. reflexivity.
Qed.
#[using="Type"] Lemma existsb_map : forall (X Y : Type) (f : X -> Y) (P : Y -> bool) l, existsb P (map f l) = existsb (fun x => P (f x)) l.
Proof. intros X Y f P l. induction l as [|x r IH]; [reflexivity|]. cbn. rewrite IH. reflexivity. Qed.
#[using="Type"] Lemma existsb_ext_in : forall (X : Type) (P Q : X -> bool) l, (forall x, In x l -> P x = Q x) -> existsb P l = existsb Q l.
Proof. intros X P Q l H. induction l as [|x r IH]; [reflexivity|]. cbn. rewrite (H x (or_introl eq_refl)), IH; [reflexivity|]. intros y Hy. apply H. right. exact Hy. Qed.
#[using="m Hfw Hbw ER"] Lemma in_allow_rename : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "N'Y='S6'='H'7&X0&S5r2%211%411(D%83721'Q3poF19&X=&XFv\2r4%3221&W1v]0r3%3321?%9251%:273%F3<21p0?1plHI1phNK1pR<M1").
Proof.
intros E cs nx Hv. apply functional_extensionality. intros z. unfold in_allow, in_vis, in_sh. cbn [rename_cs a_vis].
rewrite !existsb_map. f_equal; apply existsb_ext_in; intros p Hin;
pose proof (proj1 (forallb_forall _ _) Hv p Hin) as Hp; apply andb_prop in Hp as [H1 H2];
unfold sh_lo, sh_hi, prename; cbn [fst snd]; rewrite !(uE_rename E) by assumption; reflexivity.
Qed.
#[using="m Hfw Hbw ER"] Lemma in_ghost_rename : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "N'Y='S6'='H'7&X0&S0r2%211%411(D%83721'Q3poF19&X>&XFv\2r4%3221&W1v]0r3%3321?%9251%:273%F3<21p0?1plHI1phNK1pR<M1").
Proof.
intros E cs nx Hg. apply functional_extensionality. intros z. unfold in_ghost. cbn [rename_cs a_ghost].
rewrite existsb_map. apply existsb_ext_in. intros p Hin.
pose proof (proj1 (forallb_forall _ _) Hg p Hin) as Hp. apply andb_prop in Hp as [H1 H2].
unfold prename. cbn [fst snd]. rewrite !(uE_rename E) by assumption. reflexivity.
Qed.
#[using="nx0 e_sp0_init argH_agree m Hfw Hbw gb Hgb Hm ER"] Lemma hid_rename : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "Q3'Y='S6'='QL'H'7&X0&S5r3%211%411(D%83721'_2yR0%211pg@1;&X:&XFv\2r5%3221&W1v]0r4%3321Ar2%:3621%;3842%I3=21p0B1pl4L1plHN1phNQ01pR<Q21").
Proof.
intros E cs nx model Hv. apply functional_extensionality. intros a. unfold hid, vis.
rewrite (in_allow_rename E cs nx Hv). rewrite <- (argH_agree E (ren_env bw E) a); [|eapply env_agree_le; [apply ren_agree | exact Hgb]].
rewrite (utop_agree gb E (ren_env bw E) (ren_agree E) Hgb). reflexivity.
Qed.
#[using="m Hfw Hbw ER"] Lemma maps_match_rename : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "QA'Y='<'S<%211'B'_2yR0%211%4211%811'H'7&ZO&5&T2&XGv]0v\2%3221&S:r1%211%8241&S;%114%;271%=241qkNI1r2%A3K21(D%E3D21&XDr4r3%33217&XFr5%22E1&Q1&V1%11I%34Q8Q819%;3519p091p0>1pk<Q51pl8Q<1pR<Q@1").
Proof.
intros E ms. induction ms as [|[mb ml mk] ms IH]; intros l H HM; cbn [maps_match map] in *; [exact HM|].
cbn [forallb am_base am_len] in H. apply andb_prop in H as [Hm0 Hr]. apply andb_prop in Hm0 as [H1 H2].
unfold mrename, is_fog, amap_den in *. cbn [am_kind am_base am_len] in *.
rewrite ?(uE_rename E) by assumption. rewrite ?(ER E) by assumption.
destruct (is_tok_kind mk).
- destruct HM as [HM|(iv & l' & -> & Hsz & HM)]; [left; exact (IH _ Hr HM) | right].
exists iv, l'. split; [reflexivity|]. split; [exact Hsz | exact (IH _ Hr HM)].
- destruct HM as (l' & -> & HM). exists l'. split; [reflexivity | exact (IH _ Hr HM)].
Qed.
#[using="m Hfw Hbw ER"] Lemma holes_rename : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "QG'Y='Q3'<'B'_2yR0%211%4211%611'S<%811'H'7&ZO&5&T2&XGv]0v\2%3221&S:r1%211%8241&S;%114%;271%=241qkNC1%@3D18(D%D3C21'Q0&X;r5r4r3%43321r2%73N21&XFr6%22H1%:3198&Q1&V1%11M%34Q6Q61;%@3Q751p0:1p0C1pl8Q91pk<Q<1po@QD1pR<QF1").
Proof.
intros E y l ms H HF. apply Forall_forall. intros m0 Hin Hk. apply in_map_iff in Hin as (m1 & <- & Hin).
pose proof (proj1 (forallb_forall _ _) H m1 Hin) as Hmm. apply andb_prop in Hmm as [H1 H2].
unfold hole_ok, is_hole, mrename in *. cbn [am_base am_len am_kind] in *. rewrite !(uE_rename E) by assumption.
exact (proj1 (Forall_forall _ _) HF m1 Hin Hk).
Qed.
#[using="m Hfw Hbw ER"] Lemma fds_ok_rename : forall E f model,
match f with FdFile _ l o => evars_all (ren_ok fw bw) l && evars_all (ren_ok fw bw) o | _ => true end%bool = true ->
fds_ok E f model -> fds_ok (ren_env bw E) (frename fw f) model.
Proof.
intros E f model Hv H. destruct f as [|k len off|]; try exact H.
apply andb_prop in Hv as [Hl Ho]. cbn [frename].
destruct H as [p [c (H1 & H2 & H3 & H4 & H5)]]. exists p, c.
rewrite !(uE_rename E) by assumption. rewrite !(ER E) by assumption. rewrite eb_ren. repeat split; assumption.
Qed.
#[using="m Hfw Hbw ER"] Lemma hreplay_rename : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "Q>'Y='<'T?%211'H'7&ZO&5&T2&XGv]0v\2%3221&T@r1%211%8241&TB%114%;271%=241qj:C1%@3D18(D%D3C21'B'_2yR0%211%4211%M11&X<&XFr3%22G1&Q1&TD%11Kr2%44Q5Q521%9261%:283%Q63<21p0C1pj8Q91pR<Q=1").
Proof.
intros E h. induction h as [|[b n|b n] h IH]; intros H; [reflexivity| |];
cbn [forallb hop_b hop_n] in H; apply andb_prop in H as [H0 Hr]; apply andb_prop in H0 as [H1 H2];
cbn [map hrename hreplay]; rewrite (IH Hr); rewrite ?(uE_rename E) by assumption; rewrite ?(ER E) by assumption; reflexivity.
Qed.
#[using="nx0 e_sp0_init argH_agree SINV_agree m Hfw Hbw gb Hgb Hm ER"] Lemma cs_ok_rename : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "QI'Y='S6&R8y5'_2yR0%211%5241'@y8%611%311p061'QL'='H'7&SE&XGv]0v\2%3221r5%6221(D%:3921'<'YM%211&YJ&S4r6%211%411(?%118%E3831'X4r8r7r4%4532:C1&XFr9%22H1&W1%13K86%:5318@Ip071p0=1p0I1plHQ51pl4Q71pRFQ91pTNQ?1phNQF1pR<QH1").
Proof.
intros E cs R FULL model nx Hv Hlog HC.
unfold csvars_all in Hv.
apply andb_prop in Hv as [Hv Hhlz]. apply andb_prop in Hv as [Hv Hhna].
apply andb_prop in Hv as [Hv Hfd]. apply andb_prop in Hv as [Hv Hbrk]. apply andb_prop in Hv as [Hv Hgh].
apply andb_prop in Hv as [Hv Hvis]. apply andb_prop in Hv as [Hv Hmaps]. apply andb_prop in Hv as [Hregs Hkn].
pose proof (hid_rename E cs nx model Hvis) as HH.
pose proof (allowA_rename E cs nx Hvis Hgh) as HA.
assert (HMr : Mr (ren_env bw E) (rename_cs fw cs nx) model FULL = Mr E cs model FULL) by (unfold Mr; rewrite HH; reflexivity).
pose proof (utop_agree gb E (ren_env bw E) (ren_agree E) Hgb) as HU.
assert (HSP : uE (ren_env bw E) e_sp0 = uE E e_sp0).
{ unfold uE. rewrite (edenot_agree' nx0 E _ e_sp0 (env_agree_le _ _ _ _ (ren_agree E) Hgb) e_sp0_init). reflexivity. }
pose proof (sppg_agree gb E (ren_env bw E) (ren_agree E) Hgb) as HSG.
destruct HC; constructor; cbn [rename_cs a_ss a_maps a_totsz a_ylo a_eager a_vis a_ghost a_abytes a_brk a_fd a_tidset a_hna a_hlz kn mk_ss s_regs s_log s_know s_pc s_next] in *;
rewrite ?HA, ?HMr, ?HU, ?HSP, ?HSG; try assumption.
- apply regs_ok_rename; assumption.
- reflexivity.
- apply know_ok_rename; assumption.
- apply fds_ok_rename; assumption.
- apply maps_match_rename; assumption.
- apply holes_rename; assumption.
- apply Forall_forall. intros m0 Hin Hk. apply in_map_iff in Hin as (m1 & <- & Hin).
pose proof (proj1 (forallb_forall _ _) Hmaps m1 Hin) as Hmm. apply andb_prop in Hmm as [H1 H2].
unfold amap_den, mrename in *. cbn [am_base am_len am_kind] in *. rewrite !(ER E) by assumption.
exact (proj1 (Forall_forall _ _) co_none0 m1 Hin Hk).
- apply Forall_forall. intros m0 Hin Hk a Ha. apply in_map_iff in Hin as (m1 & <- & Hin).
pose proof (proj1 (forallb_forall _ _) Hmaps m1 Hin) as Hmm. apply andb_prop in Hmm as [H1 H2].
unfold mrename in *. cbn [am_base am_len am_kind] in *. rewrite !(ER E) in Ha by assumption.
exact (proj1 (Forall_forall _ _) co_kinds0 m1 Hin Hk a Ha).
- rewrite (ER E) by assumption. assumption.
- intros a. rewrite HH, (in_ghost_rename E cs nx Hgh). exact (co_zero0 a).
- eapply SINV_agree; [eapply env_agree_le; [apply ren_agree | exact Hgb] | assumption].
- unfold RNA in *. rewrite (hreplay_rename E) by assumption. assumption.
- unfold RLZ in *. rewrite (hreplay_rename E) by assumption. assumption.
Qed.
End RenameCS.
#[using="e_sp0_init argH_agree SINV_agree"] Lemma rename_sound : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "R3'='Y='S6&R8y5'_2yR0%211%5241'@y8%611%311p061'QL'<'B%12AA%311'Nv^<r8%3221'X4r7r6r5r4%5574321'H%E1L&VDr:%231<6(4r3%22Q21%83741'I'G&Z9r<r;r1%43321r9%G53D1IF'Q3&VL%11G%21B%F3421%=261%>291qR>QE1%A2QF1p0C1p0M1p0Q41pi0QI1pkJQ:1pl4Q?1pRFQA1pTNQG1phNQN1pR<R01pj4R21").
Proof.
intros gb E cs R FULL model m cs' Hgb HC H. unfold node_rename in H.
destruct (forallb (fun p => Nat.leb gb (fst p) && Nat.leb gb (snd p)) m) eqn:Hm; [|discriminate].
destruct (mk_fwd m) as [fw|] eqn:Hfw; [|discriminate].
destruct (mk_bwd m) as [bw|] eqn:Hbw; [|discriminate].
match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
injection H as <-. apply andb_prop in Hc as [Hv Hlog].
exists (ren_env bw E). split; [exact (ren_agree m bw Hbw gb Hm E)|]. split; [|reflexivity].
match goal with |- cs_ok _ (with_ss _ (mk_ss _ _ _ ?NX)) _ _ _ =>
change (cs_ok (ren_env bw E) (rename_cs fw cs NX) R FULL model) end.
apply (cs_ok_rename m fw bw Hfw Hbw gb Hgb Hm); [exact Hv | exact (co_log _ _ _ _ _ HC) | exact HC].
Qed.
#[using="e_sp0_init argH_agree SINV_agree"] Lemma compact_sound : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "QM'='Y='S6&R8y5'_2yR0%211%5241'@y8%611%311p061'QL'Nv^<r7%3221'X4r6r5r4r3%5574321'H%A1H&V8r9%221<(4%12M8%73631'I'G&Z9r;r:r1%43321r8%F53D1HE'Q3&VL%11G%21A%E3421%=261%>291qR>Q@1%A2QA1p0C1p0L1p0Q31pi0QD1pl4Q91pRFQ;1pTNQA1phNQH1pR<QJ1pj4QL1").
Proof. intros gb E cs R FULL model cs' Hgb HC H. unfold node_compact in H. eapply rename_sound; eassumption. Qed.
#[using="SEGS_in_hull HULL_ok"] Lemma abstractcell_sound : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "QD'Y='S6&R8y5'_2yR0%211%5241'@y8%611%311p061'QL'Y@'Q3'X4r8r7r6r5r4%6554321'H%@1G&V4v0r3%342;71(4r2%22N1%93841'Gr:%C518BA@&VL%11:r9%311%A3I31%8261p0:1p0E1pi0Q;1pl:N1pgFQ01pl4Q21pRFQ41pTNQ:1phNQA1pR<QC1").
Proof.
intros E cs R FULL model b n cs' HC H. unfold node_abstractcell in H.
destruct (split_lit b) as [bb bo]. cbv zeta in H.
destruct (kunk_covered A (kn cs) (KUnk (SA bb bo) (ELit n))) eqn:Hcov; [|discriminate].
injection H as <-. split; [|apply pc_set_kn].
apply cs_ok_set_kn; [exact HC|]. constructor.
- eapply kunk_covered_sound; [exact (co_know _ _ _ _ _ HC) | exact Hcov].
- eapply know_ok_cutout; [exact (co_know _ _ _ _ _ HC) | intros; reflexivity].
Qed.
#[using="Type"] Lemma hw_apply_true_incl : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "E'<'YE%211'YL'=&ZKr1&TFr4r3r2(D%544321%83<71r5%:3>51p031pS8@1po>>1pg@@1pm:B1").
Proof.
induction r as [|X r IH]; intros a x K H; [exact H|]. cbn [hw_apply] in H.
destruct X as [a' w v| | | | | | | | |]; cbn in H;
try (destruct H as [H|H]; [left; exact H | right; eapply IH; exact H]).
destruct (saddr_eqb a' a); [right; eapply IH; exact H|].
destruct H as [H|H]; [left; exact H | right; eapply IH; exact H].
Qed.
#[using="Type"] Lemma hw_apply_true_vars : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "I'<'YE%211'YL'='H'7&U=r1r4%3221(D%73621r2&TFr5r3%342816%;251%>3=18p081pgFA1po>B1pg@D1pm:F1").
Proof.
induction r as [|X r IH]; intros a x b H; [reflexivity|]. cbn [APK.kn_vars_lt] in H. apply andb_prop in H as [HX Hr].
cbn [hw_apply]. destruct X as [a' w v| | | | | | | | |]; cbn [APK.kn_vars_lt]; rewrite ?HX, ?(IH a x b Hr); try reflexivity.
destruct (saddr_eqb a' a); [exact (IH a x b Hr)|]. cbn [APK.kn_vars_lt]. rewrite HX, (IH a x b Hr). reflexivity.
Qed.
#[using="Type"] Lemma hw_apply_ok : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "QD'Y='_2yR0%211'@y8%511%311p051'<'YE%211'YL'=&Z6vZJr5r4r3%544321'H'7&U=r2%2217(D%63521'G&XIr7&Y<&TH%12@?%3241%635@1r6&TF(9%24FED1%I4H541(3%11G%D214%G3F1B%A251p0C1p0K1po>Q21pg@Q41pk0Q61pTDQ:1pR<QC1").
Proof.
intros E M k a x. induction k as [|X r IH]; intros HK Hv.
- split; [constructor | reflexivity].
- apply Forall_cons_iff in HK as [HX Hr]. cbn [APK.kn_vars_lt] in Hv. apply andb_prop in Hv as [HvX Hvr].
assert (AG : forall e, env_agree x E (upd E x e)) by (intros; apply upd_agree).
assert (KEEP : forall e, kentry_ok SEGS (upd E x e) M X).
{ intros e. apply (@Forall_inv _ (kentry_ok SEGS (upd E x e) M) X []).
eapply (know_ok_agree' x); [apply AG | | constructor; [exact HX | constructor]].
cbn [APK.kn_vars_lt]. rewrite HvX. reflexivity. }
assert (KEEPV : APK.kentry_vars_lt (Datatypes.S x) X = true) by (eapply kentry_vars_lt_mono; [exact HvX | lia]).
cbn [hw_apply hw_val].
destruct X as [a' w v| | | | | | | | |];
try (destruct (IH Hr Hvr) as [IH1 IH2]; split; [constructor; [apply KEEP | exact IH1] | cbn [APK.kn_vars_lt]; rewrite KEEPV, IH2; reflexivity]).
destruct (saddr_eqb a' a) eqn:Hs.
+
split.
* constructor.
-- cbn [kentry_ok] in HX |- *. destruct HX as (Hw & Hf & Hrd).
cbn [APK.kentry_vars_lt APK.saddr_vars_lt] in HvX. apply andb_prop in HvX as [Hva Hvv].
assert (Ea : adenot (upd E x (edenot E v)) a' = adenot E a').
{ unfold adenot. rewrite <- (edenot_agree' x E _ (a_base a') (AG _) Hva). reflexivity. }
assert (Es : estart (upd E x (edenot E v)) a' = estart E a').
{ unfold estart. rewrite <- (edenot_agree' x E _ (a_base a') (AG _) Hva). reflexivity. }
split; [exact Hw|]. split; [unfold flat in *; rewrite ?Es; exact Hf|].
rewrite Ea. cbn [edenot]. rewrite upd_at. exact Hrd.
-- eapply (know_ok_agree' x); [apply AG | apply hw_apply_true_vars; exact Hvr |].
apply Forall_forall. intros K HK'. apply hw_apply_true_incl in HK'. exact (proj1 (Forall_forall _ _) Hr K HK').
* cbn [APK.kn_vars_lt APK.kentry_vars_lt]. cbn [APK.kentry_vars_lt] in KEEPV. apply andb_prop in KEEPV as [Ka _].
rewrite Ka. cbn [APK.expr_vars_lt]. replace (Nat.ltb x (Datatypes.S x)) with true by (symmetry; apply Nat.ltb_lt; lia). cbn [andb].
eapply kn_vars_lt_mono'; [apply hw_apply_true_vars; exact Hvr | lia].
+ destruct (IH Hr Hvr) as [IH1 IH2]. split; [constructor; [apply KEEP | exact IH1] | cbn [APK.kn_vars_lt]; rewrite KEEPV, IH2; reflexivity].
Qed.
#[using="Type"] Lemma hw_go_ok : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "QH'<'Y@%211'Y='_2yR0%211'@y8%511%311p051'YE%=11'=&Z6vZJr4r3r2%544321'H'7&U=%1256(D%53421'I'G&Z9r7r1%33?21r6&TGr5r8%3321D%G4F751&M&;%12Q85%32I1%D216%G3F1C%A271%B2>1qR>Q<1%E2Q=1p0G1p0N1po>Q51pk0Q71pTDQ:1pR<QC1ph4QE1").
Proof.
induction bs as [|b r IH]; intros E M k x HK Hv.
- exists E. split; [apply env_agree_refl|]. cbn [hw_go length]. rewrite Nat.add_0_r. split; assumption.
- cbn [hw_go length]. destruct (hw_apply_ok E M k (sa_of b) x HK Hv) as [H1 H2].
destruct (IH _ M _ (Datatypes.S x) H1 H2) as (E' & Hag & HK' & Hv').
exists E'. split; [|split; [exact HK' | rewrite <- Nat.add_succ_comm; exact Hv']].
apply (env_agree_trans _ _ (upd E x (edenot E (hw_val k (sa_of b)))) _); [apply upd_agree | eapply env_agree_le; [exact Hag | lia]].
Qed.
#[using="e_sp0_init argH_agree SINV_agree"] Lemma havocwords_sound : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "R0'Y='S6&R8y5'_2yR0%211%5241'@y8%611%311p061'QL'<'Y@%211'X4r7r6r5r4r3%6554321'H%A1H&VBv^<%231:6(4r2%22N1%83741'I'G&Z9r:r1%33;21&VIr9%211%73165%9251r8%L58H1KJ'Q3&VL%11K%219%J3421%A261%B291qR>QE1%E2QF1p0G1p0Q11pi0QH1ph4Q:1pl4Q>1pRFQ@1pTNQF1phNQM1pR<QO1").
Proof.
intros E cs R FULL model bs cs' HC H. unfold node_havocwords in H.
destruct (fresh_ok nx0 cs) eqn:Hf; [|discriminate]. injection H as <-.
destruct (fresh_ok_parts cs Hf) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
destruct (hw_go_ok bs E (Mr E cs model FULL) (kn cs) (nxt cs) (co_know _ _ _ _ _ HC)) as (E' & Hag & HK' & _).
{ rewrite kn_vars_lt_eq. rewrite <- kn_vars_lt_eq. exact Fkn. }
exists E'. split; [split; [eapply env_agree_le; [exact Hag | exact Fle] | exact Hag]|]. split; [|reflexivity].
pose proof (cs_ok_agree E E' cs R FULL model Hag Hf HC) as HC2.
replace (with_ss cs (mk_ss (s_pc (a_ss cs)) (s_regs (a_ss cs)) (hw_go (s_know (a_ss cs)) bs (s_next (a_ss cs))) (s_next (a_ss cs) + length bs)))
with (set_kn (bump cs (length bs)) (hw_go (kn cs) bs (nxt cs))) by reflexivity.
apply cs_ok_set_kn.
- destruct HC2; constructor; cbn [bump with_ss a_ss mk_ss s_regs s_log s_know kn a_maps a_totsz a_ylo a_eager a_vis a_abytes a_brk a_fd a_tidset a_hna a_hlz];
try assumption; reflexivity.
- unfold Mr. change (hid E' (bump cs (length bs)) model) with (hid E' cs model).
rewrite (hid_agree (nxt cs) E E' cs model Hag Fle Fallow). exact HK'.
Qed.
#[using="Type"] Lemma respell_ok_sound : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "Q6'Y='_2yR0%211'@y8%511%311p051'<'YE%211'Y@&Z6vZJr5r4r3%544321'H'7&W3r2%23761(D%63521&Y<r7%221<%322<%;3K21p061p0>1pi@E1pg@F1pk0H1pTDL1pR<Q51").
Proof.
intros E M k a e HK H. unfold respell_ok in H.
destruct (decide_branch k BC_EQ a e) as [[|]|] eqn:Hd.
- pose proof (decide_branch_sound SEGS E M k BC_EQ a e true HK Hd) as Heq. cbn [branch_taken] in Heq. apply bv_eqb_eq in Heq. exact Heq.
- destruct (erange k (mkAlu ALU_SUB a e)) as [[lo hi]|] eqn:Hr; [|discriminate].
apply andb_prop in H as [H0 H1]. apply Z.eqb_eq in H0. apply Z.eqb_eq in H1. subst lo hi.
pose proof (erange_sound SEGS E M k _ 0 0 HK Hr) as Hb. rewrite mkAlu_denot in Hb.
cbn [alu64 alu] in Hb. rewrite bv_sub_unsigned in Hb. unfold bv_wrap in Hb.
pose proof (u64_range (edenot E a)) as Ra. pose proof (u64_range (edenot E e)) as Re.
apply bv_eq. change (bv_modulus 64) with (2 ^ 64)%Z in Hb. unfold two64 in *.
assert (Hm : ((bv_unsigned (edenot E a) - bv_unsigned (edenot E e)) mod 2 ^ 64 = 0)%Z) by lia.
apply Z.mod_divide in Hm; [|lia]. destruct Hm as [q Hq]. assert (q = 0)%Z by nia. subst q. lia.
- destruct (erange k (mkAlu ALU_SUB a e)) as [[lo hi]|] eqn:Hr; [|discriminate].
apply andb_prop in H as [H0 H1]. apply Z.eqb_eq in H0. apply Z.eqb_eq in H1. subst lo hi.
pose proof (erange_sound SEGS E M k _ 0 0 HK Hr) as Hb. rewrite mkAlu_denot in Hb.
cbn [alu64 alu] in Hb. rewrite bv_sub_unsigned in Hb. unfold bv_wrap in Hb.
pose proof (u64_range (edenot E a)) as Ra. pose proof (u64_range (edenot E e)) as Re.
apply bv_eq. change (bv_modulus 64) with (2 ^ 64)%Z in Hb. unfold two64 in *.
assert (Hm : ((bv_unsigned (edenot E a) - bv_unsigned (edenot E e)) mod 2 ^ 64 = 0)%Z) by lia.
apply Z.mod_divide in Hm; [|lia]. destruct Hm as [q Hq]. assert (q = 0)%Z by nia. subst q. lia.
Qed.
#[using="Type"] Lemma respell_sound : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "QD'Y='S6&R8y5'_2yR0%211%5241'@y8%611%311p061'QL'='Y@'X4r8r7r6r5r4%6554321'H%@1G&VEr3%23:61(4r2%22M1%83741'Gr:%B518A@?'Q3&VL%11;r9%311%A3531%9271p0;1p0E1pi0Q;1pi@N1pm:Q01pl4Q21pRFQ41pTNQ:1phNQA1pR<QC1").
Proof.
intros E cs R FULL model r e cs' HC H. unfold node_respell in H.
destruct (Nat.ltb 0 r && Nat.ltb r 32 && APK.expr_vars_lt (nxt cs) e && respell_ok (kn cs) (reg cs r) e)%bool eqn:Hc; [|discriminate].
injection H as <-.
apply andb_prop in Hc as [Hc Hok]. apply andb_prop in Hc as [Hc _]. apply andb_prop in Hc as [H1 H2]. apply Nat.ltb_lt in H1. apply Nat.ltb_lt in H2.
pose proof (respell_ok_sound E _ (kn cs) (reg cs r) e (co_know _ _ _ _ _ HC) Hok) as Heq.
split; [|reflexivity].
destruct HC; constructor; cbn [set_reg with_ss a_ss mk_ss s_regs s_log s_know kn a_maps a_totsz a_ylo a_eager a_vis a_abytes a_brk a_fd a_tidset a_hna a_hlz]; try assumption; try reflexivity.
apply regs_ok_respell; [assumption | lia | unfold reg in Heq; symmetry; exact Heq].
Qed.
#[using="Type"] Lemma self_jump_word : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "Q5'QH'H'@'_2yR0%211%411&QJr1%211(1%116%;3631yQ0%;11%=11&QGvZJ&QIr2%211%5241(4&_1&RM%22<1%42<1%J3<61'7&Z>r3%22>1(D%Q03521p071p0G1pl8Q41").
Proof. intros ms Hs Hf. unfold is_self_jump. rewrite Hs, Hf. vm_compute. reflexivity. Qed.
Definition LCOK (lc : option loopctx) (D : TSet) (E : env) (fs : Fs.Fs) : Prop :=
match lc with
| None => True
| Some (LC h nx lo hi) => ((nx0 <= lo)%nat /\ (lo <= hi)%nat /\ length (s_regs (a_ss nx)) = 32%nat) /\
forall E' R' F' m', env_agree lo E E' -> cs_ok E' nx R' F' m' -> m_fs m' = fs ->
srealizes SEGS scfg (cfg R' h F' m') D
| Some (JC j js sk b lo) => ((nx0 <= b)%nat /\ (b <= lo)%nat /\ length (s_regs (a_ss js)) = 32%nat) /\
forall E' R' F' m', env_agree b E E' -> cs_ok E' js R' F' m' -> m_fs m' = fs ->
srealizes SEGS scfg (cfg R' (pc js) F' m') (sd D E' fs sk)
end.
#[using="Type"] Lemma LCOK_bnd : forall lc D E fs, LCOK lc D E fs -> (nx0 <= match lc with Some c => lc_bnd c | None => nx0 end)%nat.
Proof. intros [[h nx lo hi|j js sk b lo]|] D E fs HL; cbn [LCOK lc_bnd] in *; [destruct HL as [(H1 & H2 & _) _]; lia | destruct HL as [(H1 & _ & _) _]; lia | lia]. Qed.
Definition lc_guard (lc : option loopctx) (cs : acs) : bool :=
match lc with Some c => Nat.leb (lc_bnd c) (nxt cs) | None => true end.
#[using="Type"] Lemma LCOK_agree : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "Q5'@'UI%211&ZC'Y=&QF'S6&WLr6r5r4r2%544321'H'7&XCr7%2216(D%63521&Z9&VIr3%211%431@?r9r8%D421CBp041p0:1p0B1phNI1piNK1pR>M1pR<N1pR:Q01pkDQ21").
Proof.
intros [[h nx lo hi|j js sk b lo]|] D E E' fs cs HL Hg Hag; [| |exact I]; cbn [LCOK lc_guard lc_bnd] in *;
apply Nat.leb_le in Hg; destruct HL as [(Hn0 & Hlh & Hlen) HL]; (split; [split; [exact Hn0 | split; [exact Hlh | exact Hlen]]|]);
intros E2 R' F' m' Hag2; apply HL; (eapply env_agree_trans; [eapply env_agree_le; [exact Hag | lia] | exact Hag2]).
Qed.
#[using="Type"] Lemma LCOK_agree_gb : forall lc D E E' fs,
LCOK lc D E fs -> env_agree (match lc with Some c => lc_bnd c | None => nx0 end) E E' -> LCOK lc D E' fs.
Proof.
intros [[h nx lo hi|j js sk b lo]|] D E E' fs HL Hag; [| |exact I]; cbn [LCOK lc_bnd] in *;
destruct HL as [(Hn0 & Hlh & Hlen) HL]; (split; [split; [exact Hn0 | split; [exact Hlh | exact Hlen]]|]);
intros E2 R' F' m' Hag2; apply HL; (eapply env_agree_trans; [eapply env_agree_le; [exact Hag | lia] | exact Hag2]).
Qed.
#[using="HOLES_agree"] Lemma cont_agree : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "SO'='@'UI%211'VM'S6'W<'Y='QL&ZC'H'SC&S?vZJvQAv0v^<vQEv[Ev[Dv[CvQ@vQDr:r9r8r5r7%@??>=<;:987654321(RLr4%211%F3E41&WLr2&QNr3%211%54>481'7&XC%12B@(D%Q13421(?'QM%211%A11&R8y5'_2yR0%211%5241y8%511%QG11p051'X4r=r1%35O2IK1rA%L1M%O42Q9Q61r;%11D'ZHv^I&XLr6&VLr@%211%55QM41Q@Q<&XHr<%Q:1Q?r?%443QD21%=4R3<61p0?1p0B1p0F1pl4R<1pRFL1pTNQ11pR<R@1'G&Z9%13R:>QL&VI%11>%431AQO%6241%Q55R5AR1QKQM&QF%QN1Q6%RH32QM1%L1Q5%O5RGN1R:R6r>%R311%L4Q<I1O%Q54RKQ441p071p0;1p0=1pl6S41pRHQD1pU0QI1pR>S81p0I1p0R21p0R71p0R=1p0RD1pR:S<1pl4S>1pR<S@1pm@SB1pi0SD1phNSE1pk0SG1pkDSI1pj0SM1pgNSN1").
Proof.
intros bfuel fuel lc k cs cs' s E model D Hc HL Hg HD IH E' R' FULL' model' [Hag Hag2] HC' Hfs.
rewrite (sd_agree D E E' (m_fs model) s Hag (check_vars _ _ _ _ _ _ Hc)), <- Hfs.
apply (IH E' R' FULL' model' HC'); [|exact HD]. rewrite Hfs. eapply LCOK_agree; [exact HL | exact Hg | exact Hag2].
Qed.
#[using="IT_ok SEGS_wx SEGS_in_hull HULL_ok SHADOW_ok argH_high e_sp0_init argH_agree SINV_frame SINV_agree HOLES_agree HOLES_nil HOLES_flat node_sys_sound node_brk2_sound node_mmap2_sound node_mmapin_sound node_mprotect2_sound node_exit_sound node_x_sound node_join_sound node_ext_sound node_emit_sound node_ext2_sound HS_sound"] Theorem check_sound : ltac2:(TCodec.tc2 tcn__AsanPlanSoundK "RB'='@'UI%211'VM'S6'W<'H'SC&S?vZJvQAv0v^<vQEv[Ev[Dv[CvQ@vQDr5r6r4r2r3%@??>=<;:987654321(RLr1%211%F3E41'Y=&R8y5'_2yR0%211%5241y8%511%Q611p051'QL&ZC'X4r8%25I1GEF&WLr;&QN%11I%443KM1(?'QM%211%N11'ZHv^I&XLr7&VL%11=%45QC31Q8Q9&XH%?1Q;r:%34Q;E21%;4QH:51p0=1p0B1p0H1pR:L1pl4N1pRFQ01pTNQ51pR<Q<1p0Q>1pm@R61phNR81pm8R:1pkDR<1pgNR@1pj0RA1").
Proof.
induction fuel as [|fuel IH]; intros bfuel lc p cs s Hc E R FULL model D HC HL HD; [discriminate|].
cbn [APK.check] in Hc.
match type of Hc with (if negb ?g then _ else _) = _ => destruct g eqn:Hg; [|discriminate] end. cbn [negb] in Hc.
assert (CONT : forall k cs' s', CHECK bfuel fuel lc cs' k = COk s' ->
forall E' R' FULL' model', env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> cs_ok E' cs' R' FULL' model' ->
m_fs model' = m_fs model -> srealizes SEGS scfg (cfg R' (pc cs') FULL' model') (sd D E (m_fs model) s')).
{ intros k cs' s' Hk. eapply cont_agree; [exact Hk | exact HL | exact Hg | exact HD | intros; eapply IH; eassumption]. }
assert (SAME : forall k cs' s', CHECK bfuel fuel lc cs' k = COk s' -> cs_ok E cs' R FULL model ->
srealizes SEGS scfg (cfg R (pc cs') FULL model) (sd D E (m_fs model) s')).
{ intros k cs' s' Hk HC'. refine (CONT k cs' s' Hk E R FULL model (conj (env_agree_refl _ _) (env_agree_refl _ _)) HC' eq_refl). }
destruct p as [stops k|e mid k1 k2|ce cmid ck1 ck2|db1 db2 dk1 dk2|sb1 sn1 sb2 sn2 k| |K k|jb joff jn k|ixs k|db dn k|gws k|bm k|hrs k|hbK k|r logc fb k|y k|ma mb|ia ib ic|qa qb|ka kb|x args k|xid xargs k|eid eargs k|bid bargs kb1 kb2|lJ lN linv lbody lk| |h| | |fi fsz fk|gi gsz gk|gb gn gk2|ub un uk|hlo hhi hk|ilo ihi ik|djp drs dk|rnm rnk|cpk|vj vjs vlo vka vk|mj|ab an ak|hws hwk|rsr rse rsk|iha ihb ihc|hai halo hahi hanl hanh hak|wb woff wn wlo whi wk|lha lhb].
-
destruct (run_block_gc SEGS IT _ KC bfuel (stops ++ STOPS A) cs) as [cs1|] eqn:Hrb; [|discriminate].
pose proof (LCOK_bnd lc D E (m_fs model) HL) as Hgb.
eapply run_block_gc_sound; [exact Hgb | exact Hrb | exact HC |].
intros E' R' FULL' model' Hag HC1 Hfs. exact (CONT k cs1 s Hc E' R' FULL' model' Hag HC1 Hfs).
-
destruct (APK.expr_vars_lt nx0 e) eqn:Hv; [|discriminate].
destruct (erange (kn cs) e) as [[lo hi]|] eqn:Hr; [|discriminate].
destruct (Z.leb lo mid && Z.ltb mid hi)%bool.
2: {
pose proof (erange_sound SEGS E _ (kn cs) e lo hi (co_know _ _ _ _ _ HC) Hr) as Hb.
destruct (Z.leb_spec hi mid) as [Hle|Hgt]; [exact (SAME k1 _ s Hc HC) | exact (SAME k2 _ s Hc HC)]. }
destruct (CHECK bfuel fuel lc (set_kn cs (KRange e lo mid :: kn cs)) k1) as [s1|] eqn:H1; [|discriminate].
destruct (CHECK bfuel fuel lc (set_kn cs (KRange e (mid+1) hi :: kn cs)) k2) as [s2|] eqn:H2; [|discriminate].
injection Hc as <-. cbn [sd].
destruct (split_sound cs e mid lo hi E R FULL model HC Hr) as [HCl HCr].
destruct (Z.leb_spec (bv_unsigned (edenot E e)) mid) as [Hle|Hgt].
+ exact (SAME k1 _ s1 H1 (HCl Hle)).
+ exact (SAME k2 _ s2 H2 (HCr ltac:(lia))).
-
destruct (erange (kn cs) ce) as [[lo hi]|] eqn:Hr; [|discriminate].
destruct (Z.leb lo cmid && Z.ltb cmid hi)%bool.
2: { cbn [negb] in Hc. destruct (Z.leb hi cmid); [exact (SAME ck1 _ s Hc HC) | exact (SAME ck2 _ s Hc HC)]. }
cbn [negb] in Hc. cbv zeta in Hc.
destruct (split_sound cs ce cmid lo hi E R FULL model HC Hr) as [HCl HCr].
destruct (kn_contra (kn (set_kn cs (KRange ce lo cmid :: kn cs)))) eqn:Hk1.
{ destruct (Z.leb_spec (bv_unsigned (edenot E ce)) cmid) as [Hle|Hgt].
- exfalso. exact (kn_contra_sound E _ _ (co_know _ _ _ _ _ (HCl Hle)) Hk1).
- exact (SAME ck2 _ s Hc (HCr ltac:(lia))). }
destruct (kn_contra (kn (set_kn cs (KRange ce (cmid + 1) hi :: kn cs)))) eqn:Hk2.
{ destruct (Z.leb_spec (bv_unsigned (edenot E ce)) cmid) as [Hle|Hgt].
- exact (SAME ck1 _ s Hc (HCl Hle)).
- exfalso. exact (kn_contra_sound E _ _ (co_know _ _ _ _ _ (HCr ltac:(lia))) Hk2). }
destruct (CHECK bfuel fuel lc (set_kn cs (KRange ce lo cmid :: kn cs)) ck1) as [s1|] eqn:H1; [|discriminate].
destruct (CHECK bfuel fuel lc (set_kn cs (KRange ce (cmid+1) hi :: kn cs)) ck2) as [s2|] eqn:H2; [|discriminate].
destruct (shape_eqb s1 s2) eqn:Hse; [|discriminate]. injection Hc as <-. apply shape_eqb_eq in Hse. subst s2.
destruct (Z.leb_spec (bv_unsigned (edenot E ce)) cmid) as [Hle|Hgt].
+ exact (SAME ck1 _ s1 H1 (HCl Hle)).
+ exact (SAME ck2 _ s1 H2 (HCr ltac:(lia))).
-
destruct (node_casedisj cs db1 db2) as [[csa csb]|] eqn:Hn; [|discriminate].
destruct (CHECK bfuel fuel lc csa dk1) as [s1|] eqn:H1; [|discriminate].
destruct (CHECK bfuel fuel lc csb dk2) as [s2|] eqn:H2; [|discriminate].
destruct (shape_eqb s1 s2) eqn:Hse; [|discriminate]. injection Hc as <-. apply shape_eqb_eq in Hse. subst s2.
destruct (casedisj_sound cs db1 db2 csa csb E R FULL model HC Hn) as [[HC' Hpc]|[HC' Hpc]]; rewrite <- Hpc.
+ exact (SAME dk1 _ s1 H1 HC').
+ exact (SAME dk2 _ s1 H2 HC').
-
destruct (node_shdisj A cs sb1 sn1 sb2 sn2) as [cs1|] eqn:Hn; [|discriminate].
destruct (shdisj_sound cs sb1 sn1 sb2 sn2 cs1 E R FULL model HC Hn) as [HC' Hpc]. rewrite <- Hpc.
exact (SAME k _ s Hc HC').
-
destruct (kn_contra (kn cs)) eqn:Hk; [|discriminate]. exfalso.
exact (kn_contra_sound E _ (kn cs) (co_know _ _ _ _ _ HC) Hk).
-
destruct (fact_ok (kn cs) K) eqn:Hf; [|discriminate].
exact (SAME k _ s Hc (fact_sound E cs R FULL model K HC Hf)).
-
destruct (node_join SEGS cs jb joff jn) as [cs1|] eqn:Hn; [|discriminate].
eapply (node_join_sound jb joff jn cs cs1 E R FULL model); [exact HC | reflexivity | exact Hn |]. exact (CONT k cs1 s Hc).
-
exact (SAME k _ s Hc (forget_sound E cs R FULL model ixs HC)).
-
assert (Hpc : pc (node_droprange cs db dn) = pc cs) by (unfold node_droprange; destruct (split_lit db); reflexivity).
rewrite <- Hpc. exact (SAME k _ s Hc (droprange_sound E cs R FULL model db dn HC)).
-
rewrite <- (pc_set_kn cs (kn_keep (kn cs) gws)).
exact (SAME k _ s Hc (cs_ok_set_kn E cs R FULL model _ HC (know_ok_filter E _ _ (kn cs) (co_know _ _ _ _ _ HC)))).
-
destruct (node_bump cs bm) as [cs1|] eqn:Hn; [|discriminate].
destruct (bump_sound E cs R FULL model bm cs1 HC Hn) as [HC1 Hpc]. rewrite <- Hpc.
exact (SAME k _ s Hc HC1).
-
destruct (node_havoc nx0 cs hrs) as [cs1|] eqn:Hn; [|discriminate].
destruct (havoc_sound E cs R FULL model hrs cs1 HC Hn) as (E' & Hag & HC1 & Hpc). rewrite <- Hpc.
exact (CONT k cs1 s Hc E' R FULL model Hag HC1 eq_refl).
-
destruct (node_havocbig nx0 cs hbK) as [cs1|] eqn:Hn; [|discriminate].
destruct (havocbig_sound E cs R FULL model hbK cs1 HC Hn) as (E' & Hag & HC1 & Hpc). rewrite <- Hpc.
exact (CONT k cs1 s Hc E' R FULL model Hag HC1 eq_refl).
-
destruct (node_fresh nx0 cs r logc fb) as [cs1|] eqn:Hn; [|discriminate].
eapply (node_fresh_sound_pf r logc fb cs cs1 E R FULL model); [exact HC | reflexivity | exact Hn |]. exact (CONT k cs1 s Hc).
-
destruct (is_ecall_at SEGS cs) eqn:Hec; [|discriminate].
destruct (node_sys A nx0 y cs) as [cs1|] eqn:Hn; [|discriminate].
eapply (node_sys_sound y cs cs1 E R FULL model); [exact HC | exact Hec | exact Hn |]. exact (CONT k cs1 s Hc).
-
destruct (is_ecall_at SEGS cs) eqn:Hec; [|discriminate].
destruct (node_mmap2 A nx0 LIMIT false cs) as [[csa csb]|] eqn:Hn; [|discriminate].
pose proof (node_mmap2_nosplit_contra A nx0 LIMIT cs csa csb Hn) as Hka.
eapply (node_mmap2_sound false cs csa csb E R FULL model); [exact HC | exact Hec | exact Hn | | exact (CONT mb csb s Hc)].
intros E' R' FULL' model' _ HC' _. exfalso. exact (kn_contra_sound E' _ _ (co_know _ _ _ _ _ HC') Hka).
-
destruct (is_ecall_at SEGS cs) eqn:Hec; [|discriminate].
destruct (node_mmapin A LIMIT false cs) as [[[csa csb] cscs]|] eqn:Hn; [|discriminate].
eapply (node_mmapin_sound false cs csa csb cscs E R FULL model); [exact HC | exact Hec | exact Hn | exact (CONT ib csb s Hc)].
-
destruct (is_ecall_at SEGS cs) eqn:Hec; [|discriminate].
destruct (node_mprotect2 A LIMIT cs) as [[csa csb]|] eqn:Hn; [|discriminate].
assert (Hka : kn_contra (kn csa) = true).
{ unfold node_mprotect2 in Hn. destruct (node_mprotect A LIMIT cs); [|discriminate]. injection Hn as <- <-. reflexivity. }
eapply (node_mprotect2_sound cs csa csb E R FULL model); [exact HC | exact Hec | exact Hn | | exact (CONT qb csb s Hc)].
intros E' R' FULL' model' _ HC' _. exfalso. exact (kn_contra_sound E' _ _ (co_know _ _ _ _ _ HC') Hka).
-
destruct (is_ecall_at SEGS cs) eqn:Hec; [|discriminate].
destruct (node_brk2 A LIMIT cs) as [[csa csb]|] eqn:Hn; [|discriminate].
destruct (CHECK bfuel fuel lc csa ka) as [sa|] eqn:H1; [|discriminate].
destruct (CHECK bfuel fuel lc csb kb) as [sb|] eqn:H2; [|discriminate].
destruct (hole_only sa && hole_only sb)%bool eqn:Hho; [|discriminate]. apply andb_prop in Hho as [Hha Hhb].
injection Hc as <-.
eapply srz_conseq; [| apply sd_salt2; exact HD].
eapply (node_brk2_sound cs csa csb E R FULL model); [exact HC | exact Hec | exact Hn | exact (CONT ka csa sa H1) | exact (CONT kb csb sb H2) |].
apply hole_only_eq; assumption.
-
destruct (node_x SEGS A nx0 x args cs) as [cs1|] eqn:Hn; [|discriminate].
eapply (node_x_sound x args cs cs1 E R FULL model); [exact HC | reflexivity | exact Hn |]. exact (CONT k cs1 s Hc).
-
destruct (XN xid xargs cs) as [cs1|] eqn:Hn; [|discriminate].
eapply (node_ext_sound xid xargs cs cs1 E R FULL model); [exact HC | reflexivity | exact Hn |]. exact (CONT k cs1 s Hc).
-
destruct (XE eid eargs cs) as [[[fd ps] cs1]|] eqn:Hn; [|discriminate].
destruct (CHECK bfuel fuel lc cs1 k) as [s1|] eqn:H1; [|discriminate]. injection Hc as <-. cbn [sd].
eapply (node_emit_sound eid eargs cs fd ps cs1 E R FULL model); [exact HC | exact Hn | apply sd_has_nil; exact HD |]. exact (CONT k cs1 s1 H1).
-
destruct (XB bid bargs cs) as [[csa csb]|] eqn:Hn; [|discriminate].
destruct (CHECK bfuel fuel lc csa kb1) as [sa|] eqn:H1; [|discriminate].
destruct (CHECK bfuel fuel lc csb kb2) as [sb|] eqn:H2; [|discriminate].
injection Hc as <-. cbn [sd].
eapply (node_ext2_sound bid bargs cs csa csb E R FULL model); [exact HC | exact Hn | exact (CONT kb1 csa sa H1) | exact (CONT kb2 csb sb H2)].
-
destruct (loop_ok nx0 cs lJ lN linv) as [nhi|] eqn:Hlo; [|discriminate].
destruct (Z.eqb (pc linv) (pc cs) && entails_h A (Datatypes.S lJ) (nxt linv) cs (inst linv lJ (ELit 0)))%bool eqn:Ht; [|discriminate].
apply andb_prop in Ht as [Hpc Hent]. apply Z.eqb_eq in Hpc.
destruct (CHECK bfuel fuel (Some (LC (pc cs) (inst linv lJ (eaddz (EVar lJ) 1)) (Datatypes.S lJ) (nxt linv))) (loop_body_state lJ lN nhi linv) lbody) as [sb|] eqn:Hbody; [|discriminate].
destruct sb; try discriminate. rename Hc into Hk.
destruct (loop_ok_facts cs lJ lN linv nhi Hlo) as (Ffr & FJ & FJh & Flog & Flen & FvN & FxN & Fnhi).
destruct (fresh_ok_parts cs Ffr) as (_ & _ & _ & _ & _ & _ & Fle).
pose proof (xhi_sound SEGS E _ (kn cs) lN nhi (co_know _ _ _ _ _ HC) FxN) as HNv.
set (Nv := bv_unsigned (edenot E lN)) in *. pose proof (u64_range (edenot E lN)) as RN. fold Nv in RN.
set (D0 := sd D E (m_fs model) s).
assert (HD0 : D0 []) by (apply sd_has_nil; exact HD).
set (h := pc cs) in *.
assert (Q : forall m j E' R' F' m', j = Nv - Z.of_nat m -> 0 <= j -> env_agree (nxt cs) E E' ->
cs_ok E' (inst linv lJ (ELit j)) R' F' m' -> m_fs m' = m_fs model ->
srealizes SEGS scfg (cfg R' h F' m') D0).
{ induction m as [|m IHm]; intros j E' R' F' m' Hj Hj0 Hag HCj Hfs.
-
assert (HNe : edenot E' lN = edenot E' (ELit j)).
{ cbn [edenot]. rewrite <- (edenot_agree' (nxt cs) E E' lN Hag FvN). apply bv_eq. rewrite u_small by lia. cbn in Hj. lia. }
assert (HCN : cs_ok E' (inst linv lJ lN) R' F' m').
{ apply (proj2 (cs_ok_inst E' lJ lN linv R' F' m' ltac:(lia) Flog)). rewrite HNe.
apply (proj1 (cs_ok_inst E' lJ (ELit j) linv R' F' m' ltac:(lia) Flog)). exact HCj. }
unfold D0. rewrite (sd_agree D E E' (m_fs model) s ltac:(eapply env_agree_le; [exact Hag | exact Fle]) (check_vars _ _ _ _ _ _ Hk)).
rewrite <- Hfs. replace h with (pc (inst linv lJ lN)) by (unfold h; rewrite pc_inst; exact Hpc).
apply (IH bfuel lc lk _ s Hk E' R' F' m' D HCN); [|exact HD].
rewrite Hfs. eapply LCOK_agree; [exact HL | exact Hg | exact Hag].
-
set (E'' := upd E' lJ (Z_to_bv 64 j)).
assert (Hjlt : j < Nv) by lia.
assert (HCinv : cs_ok E'' linv R' F' m').
{ unfold E''. replace (Z_to_bv 64 j) with (edenot E' (ELit j)) by reflexivity.
apply (proj1 (cs_ok_inst E' lJ (ELit j) linv R' F' m' ltac:(lia) Flog)). exact HCj. }
assert (Hag'' : env_agree (nxt cs) E E'').
{ eapply env_agree_trans; [exact Hag|]. eapply env_agree_le; [apply upd_agree | exact FJ]. }
assert (HNE'' : edenot E'' lN = edenot E lN) by (symmetry; eapply (edenot_agree' (nxt cs)); [exact Hag'' | exact FvN]).
assert (HJ'' : ev E'' lJ = Z_to_bv 64 j) by (unfold E''; apply upd_at).
assert (HCb : cs_ok E'' (loop_body_state lJ lN nhi linv) R' F' m').
{ unfold loop_body_state, add_kn. apply cs_ok_set_kn; [exact HCinv|]. apply Forall_app. split; [|exact (co_know _ _ _ _ _ HCinv)].
constructor; [|constructor; [|constructor]]; cbn [kentry_ok edenot].
- rewrite HJ'', u_small by lia. lia.
- unfold esub. rewrite mkAlu_denot, u_sub64. cbn [edenot]. rewrite HNE'', HJ''. fold Nv. rewrite u_small by lia.
rewrite Z.mod_small by lia. lia. }
replace h with (pc (loop_body_state lJ lN nhi linv)) by exact Hpc.
refine (IH bfuel _ lbody _ SNext Hbody E'' R' F' m' D0 HCb _ HD0).
cbn [LCOK]. split.
{ split; [lia|]. split; [lia|]. unfold inst. cbn [a_ss s_regs mk_ss]. rewrite length_map. exact Flen. }
intros E3 R3 F3 m3 Hag3 HC3 Hfs3.
assert (HJ3 : ev E3 lJ = Z_to_bv 64 j) by (rewrite <- HJ''; symmetry; apply (proj1 Hag3); lia).
assert (Hnext : edenot E3 (eaddz (EVar lJ) 1) = Z_to_bv 64 (j + 1)).
{ unfold eaddz. rewrite mkAlu_denot. cbn [edenot]. rewrite HJ3. apply bv_eq. rewrite u_add64, !u_small by lia. rewrite Z.mod_small by lia. reflexivity. }
set (E4 := upd E3 lJ (Z_to_bv 64 (j + 1))).
apply (IHm (j + 1) E4 R3 F3 m3); [lia | lia | | | rewrite Hfs3; exact Hfs].
+ eapply env_agree_trans; [exact Hag''|]. eapply env_agree_trans; [eapply env_agree_le; [exact Hag3 | lia]|].
eapply env_agree_le; [apply upd_agree | exact FJ].
+ apply (proj2 (cs_ok_inst E4 lJ (ELit (j + 1)) linv R3 F3 m3 ltac:(lia) Flog)).
unfold E4. cbn [edenot]. rewrite upd_upd. rewrite <- Hnext.
apply (proj1 (cs_ok_inst E3 lJ (eaddz (EVar lJ) 1) linv R3 F3 m3 ltac:(lia) Flog)). exact HC3. }
destruct (entails_h_sound (Datatypes.S lJ) (nxt linv) E cs (inst linv lJ (ELit 0)) R FULL model HC Hent ltac:(lia)
ltac:(unfold inst; cbn [a_ss s_regs mk_ss]; rewrite length_map; exact Flen)) as (E1 & Hag1 & _ & HC1 & _).
unfold D0 in Q. apply (Q (Z.to_nat Nv) 0 E1 R FULL model); [lia | lia | eapply env_agree_le; [exact Hag1 | lia] | exact HC1 | reflexivity].
-
destruct lc as [[h nx lo hi|j' js' sk' b' lo']|]; [|discriminate|discriminate].
destruct (Z.eqb (pc cs) h && entails_h A lo hi cs nx)%bool eqn:Ht; [|discriminate]. injection Hc as <-. cbn [sd].
apply andb_prop in Ht as [Hpc Hent]. apply Z.eqb_eq in Hpc.
cbn [LCOK] in HL. destruct HL as [(Hn0 & Hlh & Hlen) HL]. cbn [lc_guard lc_bnd] in Hg. apply Nat.leb_le in Hg.
destruct (entails_h_sound lo hi E cs nx R FULL model HC Hent Hn0 Hlen) as (E' & Hag & _ & HC' & Hpc').
rewrite Hpc. exact (HL E' R FULL model Hag HC' eq_refl).
-
destruct (HS h) as [ch|] eqn:Hh; [|discriminate].
destruct (entails cs ch) eqn:He; [|discriminate]. injection Hc as <-. cbn [sd].
destruct (entails_sound E cs ch R FULL model HC He) as [HC' Hpc].
rewrite <- Hpc. exact (HS_sound h ch Hh E R FULL model HC').
-
destruct (is_ecall_at SEGS cs) eqn:Hec; [|discriminate].
destruct (node_exit cs) as [code|] eqn:Hn; [|discriminate]. injection Hc as <-. cbn [sd].
eapply node_exit_sound; eassumption.
-
discriminate Hc.
-
destruct (node_fog cs fi fsz) as [cs1|] eqn:Hn; [|discriminate].
destruct (fog_sound E cs R FULL model fi fsz cs1 HC Hn) as [HC1 Hpc]. rewrite <- Hpc. exact (SAME fk _ s Hc HC1).
-
destruct (node_fognew cs gi gsz) as [cs1|] eqn:Hn; [|discriminate].
destruct (fognew_sound E cs R FULL model gi gsz cs1 HC Hn) as [HC1 Hpc]. rewrite <- Hpc. exact (SAME gk _ s Hc HC1).
-
destruct (node_ghost LIMIT cs gb gn) as [cs1|] eqn:Hn; [|discriminate].
destruct (ghost_sound E cs R FULL model gb gn cs1 HC Hn) as [HC1 Hpc]. rewrite <- Hpc. exact (SAME gk2 _ s Hc HC1).
-
destruct (node_unvis A cs ub un) as [cs1|] eqn:Hn; [|discriminate].
destruct (unvis_sound E cs R FULL model ub un cs1 HC Hn) as [HC1 Hpc]. rewrite <- Hpc. exact (SAME uk _ s Hc HC1).
-
destruct (node_havocbrk nx0 cs hlo hhi) as [cs1|] eqn:Hn; [|discriminate].
destruct (havocbrk_sound E cs R FULL model hlo hhi cs1 HC Hn) as (E' & Hag & HC1 & Hpc). rewrite <- Hpc.
exact (CONT hk cs1 s Hc E' R FULL model Hag HC1 eq_refl).
-
destruct (node_intro nx0 cs ilo ihi) as [cs1|] eqn:Hn; [|discriminate].
destruct (intro_sound E cs R FULL model ilo ihi cs1 HC Hn) as (E' & Hag & HC1 & Hpc). rewrite <- Hpc.
exact (CONT ik cs1 s Hc E' R FULL model Hag HC1 eq_refl).
-
destruct (branch_probe IT cs) as [e|] eqn:Hbp; [|discriminate].
destruct (erange (kn cs) e) as [[lo hi]|] eqn:Hr; [|discriminate].
pose proof (LCOK_bnd lc D E (m_fs model) HL) as Hgb.
destruct (Z.ltb hi 1 || Z.ltb 0 lo)%bool eqn:Hdec.
{
destruct (run_block_gc SEGS IT _ KC bfuel (djp :: STOPS A) cs) as [cs1|] eqn:Hrb; [|discriminate].
destruct (Z.eqb (pc cs1) djp); [|discriminate].
eapply run_block_gc_sound; [exact Hgb | exact Hrb | exact HC |].
intros E' R' FULL' model' Hag HC1 Hfs. exact (CONT dk cs1 s Hc E' R' FULL' model' Hag HC1 Hfs). }
cbv zeta in Hc.
destruct (run_block_gc SEGS IT _ KC bfuel (djp :: STOPS A) (set_kn cs (KRange e lo 0 :: kn cs))) as [ca|] eqn:Hra; [|discriminate].
destruct (run_block_gc SEGS IT _ KC bfuel (djp :: STOPS A) (set_kn cs (KRange e 1 hi :: kn cs))) as [cb|] eqn:Hrb; [|discriminate].
destruct (node_diamond_join A nx0 (nxt cs) djp drs ca cb) as [csj|] eqn:Hj; [|discriminate].
destruct (split_sound cs e 0 lo hi E R FULL model HC Hr) as [HCl HCr].
destruct (diamond_join_sound (nxt cs) djp drs ca cb csj Hj) as [Ja Jb].
destruct (Z.leb_spec (bv_unsigned (edenot E e)) 0) as [Hle|Hgt].
+ rewrite <- (pc_set_kn cs (KRange e lo 0 :: kn cs)).
eapply run_block_gc_sound; [exact Hgb | exact Hra | exact (HCl Hle) |].
intros E' R' FULL' model' [Hag0 Hag1] HC1 Hfs.
destruct (Ja E' R' FULL' model' HC1) as (E'' & [Hag2a Hag2b] & HC2 & Hpc2). rewrite <- Hpc2.
change (env_agree (nxt cs) E E') in Hag1.
exact (CONT dk csj s Hc E'' R' FULL' model'
(conj (env_agree_trans _ _ _ _ Hag0 Hag2a) (env_agree_trans _ _ _ _ Hag1 Hag2b)) HC2 Hfs).
+ rewrite <- (pc_set_kn cs (KRange e 1 hi :: kn cs)).
eapply run_block_gc_sound; [exact Hgb | exact Hrb | exact (HCr ltac:(lia)) |].
intros E' R' FULL' model' [Hag0 Hag1] HC1 Hfs.
destruct (Jb E' R' FULL' model' HC1) as (E'' & [Hag2a Hag2b] & HC2 & Hpc2). rewrite <- Hpc2.
change (env_agree (nxt cs) E E') in Hag1.
exact (CONT dk csj s Hc E'' R' FULL' model'
(conj (env_agree_trans _ _ _ _ Hag0 Hag2a) (env_agree_trans _ _ _ _ Hag1 Hag2b)) HC2 Hfs).
-
destruct (node_rename _ cs rnm) as [cs1|] eqn:Hn; [|discriminate].
pose proof (LCOK_bnd lc D E (m_fs model) HL) as Hgb.
destruct (rename_sound _ E cs R FULL model rnm cs1 Hgb HC Hn) as (E' & Hag & HC1 & Hpc). rewrite <- Hpc.
rewrite (sd_agree D E E' (m_fs model) s (env_agree_le _ _ _ _ Hag Hgb) (check_vars _ _ _ _ _ _ Hc)).
eapply IH; [exact Hc | exact HC1 | eapply LCOK_agree_gb; [exact HL | exact Hag] | exact HD].
-
destruct (node_compact _ cs) as [cs1|] eqn:Hn; [|discriminate].
pose proof (LCOK_bnd lc D E (m_fs model) HL) as Hgb.
destruct (compact_sound _ E cs R FULL model cs1 Hgb HC Hn) as (E' & Hag & HC1 & Hpc). rewrite <- Hpc.
rewrite (sd_agree D E E' (m_fs model) s (env_agree_le _ _ _ _ Hag Hgb) (check_vars _ _ _ _ _ _ Hc)).
eapply IH; [exact Hc | exact HC1 | eapply LCOK_agree_gb; [exact HL | exact Hag] | exact HD].
-
destruct (via_ok nx0 cs vjs vlo) eqn:Hv; [|discriminate].
destruct (CHECK bfuel fuel lc vjs vk) as [sk|] eqn:Hk; [|discriminate].
unfold via_ok in Hv. repeat match type of Hv with (_ && _)%bool = true => apply andb_prop in Hv as [Hv ?X] end.
match goal with Hl : match s_log (a_ss vjs) with _ => _ end = true |- _ => clear Hl end.
match goal with Hl : Nat.eqb (length _) 32 = true |- _ => apply Nat.eqb_eq in Hl; rename Hl into Hlen end.
repeat match goal with Hl : Nat.leb _ _ = true |- _ => apply Nat.leb_le in Hl end.
pose proof (LCOK_bnd lc D E (m_fs model) HL) as Hgb.
assert (Hgb' : (match lc with Some c => lc_bnd c | None => nx0 end <= nxt cs)%nat).
{ destruct lc as [c|]; [apply Nat.leb_le; exact Hg | lia]. }
apply (IH bfuel (Some (JC vj vjs sk (nxt cs) vlo)) vka cs s Hc E R FULL model D HC); [|exact HD].
cbn [LCOK]. split; [split; [lia | split; [lia | exact Hlen]]|].
intros E' R' F' m' Hag HC' Hfs. rewrite <- Hfs.
apply (IH bfuel lc vk vjs sk Hk E' R' F' m' D HC'); [|exact HD].
rewrite Hfs. eapply LCOK_agree_gb; [exact HL|]. eapply env_agree_le; [exact Hag | exact Hgb'].
-
destruct lc as [[h nx lo hi|j' js' sk' b' lo']|]; [discriminate| |discriminate].
destruct (Nat.eqb mj j' && Z.eqb (pc cs) (pc js') && shape_vars_lt nx0 sk' && entails_h A lo' (nxt js') cs js')%bool eqn:Ht; [|discriminate].
injection Hc as <-.
apply andb_prop in Ht as [Ht Hent]. apply andb_prop in Ht as [Ht Hsv]. apply andb_prop in Ht as [_ Hpc]. apply Z.eqb_eq in Hpc.
cbn [LCOK] in HL. destruct HL as [(Hn0 & Hbl & Hlen) HJ].
destruct (entails_h_sound lo' (nxt js') E cs js' R FULL model HC Hent ltac:(clear -Hn0 Hbl; lia) Hlen) as (E' & Hag & _ & HC' & Hpc').
assert (Hn0l : (nx0 <= lo')%nat) by lia.
rewrite (sd_agree D E E' (m_fs model) sk' (env_agree_le nx0 lo' E E' Hag Hn0l) Hsv). rewrite Hpc.
exact (HJ E' R FULL model (env_agree_le _ _ _ _ Hag Hbl) HC' eq_refl).
-
destruct (node_abstractcell A cs ab an) as [cs1|] eqn:Hn; [|discriminate].
destruct (abstractcell_sound E cs R FULL model ab an cs1 HC Hn) as [HC1 Hpc]. rewrite <- Hpc. exact (SAME ak _ s Hc HC1).
-
destruct (node_havocwords nx0 cs hws) as [cs1|] eqn:Hn; [|discriminate].
destruct (havocwords_sound E cs R FULL model hws cs1 HC Hn) as (E' & Hag & HC1 & Hpc). rewrite <- Hpc.
exact (CONT hwk cs1 s Hc E' R FULL model Hag HC1 eq_refl).
-
destruct (node_respell cs rsr rse) as [cs1|] eqn:Hn; [|discriminate].
destruct (respell_sound E cs R FULL model rsr rse cs1 HC Hn) as [HC1 Hpc]. rewrite <- Hpc. exact (SAME rsk _ s Hc HC1).
-
destruct (is_ecall_at SEGS cs) eqn:Hec; [|discriminate].
destruct (node_mmapin A LIMIT true cs) as [[[csa csb] cscs]|] eqn:Hn; [|discriminate].
eapply (node_mmapin_sound true cs csa csb cscs E R FULL model); [exact HC | exact Hec | exact Hn | exact (CONT ihb csb s Hc)].
-
destruct (node_habs nx0 cs hai halo hahi hanl hanh) as [cs1|] eqn:Hn; [|discriminate].
destruct (habs_sound E cs R FULL model hai halo hahi hanl hanh cs1 HC Hn) as (E' & Hag & HC1 & Hpc). rewrite <- Hpc.
exact (CONT hak cs1 s Hc E' R FULL model Hag HC1 eq_refl).
-
destruct (node_absword nx0 cs wb woff wn wlo whi) as [cs1|] eqn:Hn; [|discriminate].
destruct (absword_sound E cs R FULL model wb woff wn wlo whi cs1 HC Hn) as (E' & Hag & HC1 & Hpc). rewrite <- Hpc.
exact (CONT wk cs1 s Hc E' R FULL model Hag HC1 eq_refl).
-
destruct (is_ecall_at SEGS cs) eqn:Hec; [|discriminate].
destruct (node_mmap2 A nx0 LIMIT true cs) as [[csa csb]|] eqn:Hn; [|discriminate].
assert (DEAD : forall csx kx, kn_contra (kn csx) = true ->
forall E' R' FULL' model', env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> cs_ok E' csx R' FULL' model' ->
m_fs model' = m_fs model -> srealizes SEGS scfg (cfg R' (pc csx) FULL' model') (sd D E (m_fs model) kx)).
{ intros csx kx Hk E' R' FULL' model' _ HC' _. exfalso. exact (kn_contra_sound E' _ _ (co_know _ _ _ _ _ HC') Hk). }
destruct (kn_contra (kn csa)) eqn:Hka.
{ eapply (node_mmap2_sound true cs csa csb E R FULL model); [exact HC | exact Hec | exact Hn | exact (DEAD csa s Hka) | exact (CONT lhb csb s Hc)]. }
destruct (kn_contra (kn csb)) eqn:Hkb.
{ eapply (node_mmap2_sound true cs csa csb E R FULL model); [exact HC | exact Hec | exact Hn | exact (CONT lha csa s Hc) | exact (DEAD csb s Hkb)]. }
destruct (CHECK bfuel fuel lc csa lha) as [sa|] eqn:H1; [|discriminate].
destruct (CHECK bfuel fuel lc csb lhb) as [sb|] eqn:H2; [|discriminate].
destruct (shape_eqb sa sb) eqn:Hse; [|discriminate]. injection Hc as <-. apply shape_eqb_eq in Hse. subst sb.
eapply (node_mmap2_sound true cs csa csb E R FULL model); [exact HC | exact Hec | exact Hn | exact (CONT lha csa sa H1) | exact (CONT lhb csb sa H2)].
Qed.
End Sound.
End APSK.
