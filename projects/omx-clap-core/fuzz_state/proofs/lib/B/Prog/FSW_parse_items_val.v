(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: lib/B (fs.asan-ubsan) the COMPOSITION of parse_items' member loop on image B from
   the resume after parse_string (0x85048, FSW_parse_items_loop.pib_IE, the base of FSW_parse_items_seg.pib_ss_E) to the
   resume after parse_value (0x851d0, FSW_parse_items_loop.pib_IH, the base of FSW_parse_items_seg.pib_ss_H), over the
   measured segments E, F, G of FSW_parse_items_seg.v and three call steps: skip_ws #3 (0x850b8 -> 0x850bc,
   FSW_parse_items_sw.pic_call_sw), __asan_memset (0x8516c -> 0x85170, the runtime contract HMS) and parse_value at level
   k + 1 (0x851cc -> 0x851d0). Ports of the A walk's (a working branch 4480a5df1ae)
   lib/A/FSW_parse_items_calls.v pic_call_ms_84d78 / pic_call_pv_84d98 and lib/A/FSW_parse_items_stP.v / stM.v /
   stVc.v to B's addresses and names (q at atom 9 = s1, v at atom 19 = s3; B calls skip_ws where A inlines it).
   Section PI: the Variables, Lets and Hypotheses of parse_items_spec k's entry (the A walk's FSW_parse_items_loop.v
   Section M list at B's names, `p` the entry in->p between len and tcap), and the callees
     HSW : @skip_ws_spec fx rc SK tfibsegs B
     HPV : @parse_value_spec fx rc SK tfibsegs B (Datatypes.S k)
     HMS : FSupoisonU.aintrin_realizesU tfibsegs B OSet PC_memset   (FsRt's field fr_memset, lib/B/FSH_Rt.v)
   with IE / IK / IM / IV / IH the loop.v invariants at this entry (@pib_IE fx rc SK B k ly S U W regs mem md q ot v
   text len tcap tb ms pr rest live peak cnt fail, and so on). THE STATEMENT:
     Lemma piv_val : forall dn kk x rm T lyc Sc Uc (W1 : world tfibsegs) memC mdC regsC chq pc kids keys cap Di Da peak1
         a ly' S' (W' : world tfibsegs) regs' mem' md' (Qc : world tfibsegs -> config -> Prop),
       IE dn kk x rm T lyc Sc Uc W1 memC mdC regsC chq pc kids keys cap Di Da peak1 a ly' S' W' regs' mem' md' ->
       (forall T2 lyc2 Sc2 Uc2 (W2 : world tfibsegs) mem2 md2 regs2 chq2 pc2 Da2 peak2 D Dx ly3 S3 (W3 : world tfibsegs)
           regs3 mem3 md3,
          IH dn kk x rm T2 lyc2 Sc2 Uc2 W2 mem2 md2 regs2 chq2 pc2 kids keys cap Di Da2 peak2 a D Dx ly3 S3 W3 regs3 mem3 md3 ->
          SRr tfibsegs W3 (mkCfg (mkst regs3 (Z_to_bv 64 0x851d0) mem3 (seg_rom tfibsegs)) md3) Qc) ->
       SRr tfibsegs W' (mkCfg (mkst regs' (Z_to_bv 64 0x85048) mem' (seg_rom tfibsegs)) md') Qc.
   (Proof using All: after the Section it takes every Section variable and hypothesis in declaration order.) Its steps:
     piv_step_EF : IE at 0x85048 -> segment E (keys[n] := key) -> skip_ws #3 -> segment F (`:`) -> IM at __asan_memset
     piv_step_MG : IM at __asan_memset -> the memset (the kid zeroed) -> segment G -> IV at parse_value
     piv_step_V  : IV at parse_value -> parse_value (k + 1) -> IH at 0x851d0
   rule 24: no function is proved in this file (kind: segment lemma - a composition of measured segments and call steps
   inside parse_items B; the function theorem parse_items_holds stays with its owner a Theorem Labs lane). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From Stdlib Require FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSupoison FSupoisonU FSupoisonStack FSH_YC20
FSH_Gen.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require YF0x.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import
YB1v YB1w FSH_Base FSH_Rt FSW_K FSW_K3 FSW_ret FSW_rres FSW_rd FSW_pj FSPstat FSH_Fn_reader.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require PjIn PjStruct ReaderRes WriterValue WriterSpec
  parse_items_shape.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require PjTree PjGrammar PjRoundTrip.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.Prog Require FSDocStrs.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib Require Mem MState.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B.Prog Require FSW_pj_set_heads.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B.Prog Require Import
FSW_parse_items_tbl FSW_parse_items FSW_parse_items_kit FSW_parse_items_mdl FSW_parse_items_seg FSW_parse_items_loop
FSW_parse_items_calls FSW_parse_items_mem FSW_parse_items_sw FSW_parse_items_obj.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YI14.
Fail Definition probe_SK : OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable.YI16.sink_head := _.
Fail Definition probe_SH : OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable.YI14.sink_syms := _.

(* a fact kept out of lia's sight (lia case-splits every disjunction in the context) *)
Definition piv_hide (P : Prop) : Prop := P.
Ltac piv_pd := first [ lia | match goal with H : piv_hide (_ \/ _) |- _ =>
  let H' := fresh in pose proof H as H'; unfold piv_hide in H'; destruct H'; solve [lia] end ].
(* acallee_saved of a concrete register *)
Ltac piv_acs := lazymatch goal with |- acallee_saved (bv_unsigned ?x) =>
  let z := eval vm_compute in (bv_unsigned x) in change (bv_unsigned x) with z end; unfold acallee_saved; lia.

(* ================= image-free facts ================= *)
Section F. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma piv_ew_extK : forall ws E K n, (n < K)%nat -> ew (extK E K ws) n = ew E n.
Proof.
induction ws as [|w ws IH]; intros E K n H; cbn [extK]; [reflexivity|].
rewrite IH by lia. apply ew_ewset_other. lia.
Qed.
Lemma piv_ed_extK : forall ws E K, ed (extK E K ws) = ed E.
Proof. induction ws as [|w ws IH]; intros E K; cbn [extK]; [reflexivity|]. rewrite IH. apply ed_ewset. Qed.
(* the callee-saved list R restated at the resume: each value names only q (9), v (19) and the shadow base (32) *)
Definition piv_R_ok (R : list (bv 5 * sv)) : bool :=
  forallb (fun r => negb (Z.eqb (bv_unsigned (fst r)) 0) && negb (Z.eqb (bv_unsigned (fst r)) 10) &&
    ((Z.eqb (bv_unsigned (fst r)) 8) || (Z.eqb (bv_unsigned (fst r)) 9) ||
     ((18 <=? bv_unsigned (fst r)) && (bv_unsigned (fst r) <=? 27))) &&
    forallb (fun n => Nat.eqb n 9 || Nat.eqb n 19 || Nat.eqb n 32) (pik_sv_atoms (snd r))) R.
Lemma piv_RL_ok : piv_R_ok pib_RL = true.
Proof. vm_compute. reflexivity. Qed.
Lemma piv_RL_atoms : forall r e, In (r, e) pib_RL -> forall n, In n (pik_sv_atoms e) ->
  n = 9%nat \/ n = 19%nat \/ n = 32%nat.
Proof.
intros r e Hin n Hn. pose proof piv_RL_ok as Hok. unfold piv_R_ok in Hok. rewrite forallb_forall in Hok.
pose proof (Hok _ Hin) as Hb. cbn [fst snd] in Hb. apply andb_prop in Hb as [_ Hat].
rewrite forallb_forall in Hat. pose proof (Hat n Hn) as Hn'. cbv beta in Hn'. revert Hn'.
destruct (Nat.eqb_spec n 9); [intros _; left; assumption|].
destruct (Nat.eqb_spec n 19); [intros _; right; left; assumption|].
destruct (Nat.eqb_spec n 32); [intros _; right; right; assumption|].
cbn. discriminate.
Qed.
(* the stop's callee-saved list pib_RL restated over the stop's own registers *)
Lemma piv_RL_restate : forall E' (r2 : bvmap 5 word),
  (forall r e, In (r, e) pib_RL -> YK11.getr r2 r = sv_denot E' e) -> ed E' = ed (Ereg r2 fs_extraT) ->
  ew E' 9 = YK11.getr r2 9%bv -> ew E' 19 = YK11.getr r2 19%bv -> ew E' 32 = Z_to_bv 64 SHADOW_OFF ->
  Forall (fun r => YK11.getr r2 (fst r) = sv_denot (Ereg r2 fs_extraT) (snd r)) pib_RL.
Proof.
intros E' r2 HG Hed H9 H19 H32. apply Forall_forall. intros [r e] Hin. cbn [fst snd].
rewrite (HG r e Hin). apply pik_sv_denot_agree; [exact Hed|].
intros n Hn. destruct (piv_RL_atoms r e Hin n Hn) as [ -> | [ -> | -> ] ].
- rewrite (ew_Ereg_nat r2 fs_extraT 9 9%bv eq_refl). exact H9.
- rewrite (ew_Ereg_nat r2 fs_extraT 19 19%bv eq_refl). exact H19.
- rewrite H32. change 32%nat with (32 + 0)%nat. rewrite ew_Ereg_extra. reflexivity.
Qed.
(* the registers a measured stop names *)
Lemma piv_regs_of_stop : forall E ss ms' (H : word -> bool) l, st_ok tfibsegs E ss (restrict H ms') ->
  pib_regs_are ss l = true -> Forall (fun r => YK11.getr (ms_regs ms') (fst r) = sv_denot E (snd r)) l.
Proof.
intros E ss ms' H l HS Hl. unfold pib_regs_are in Hl. rewrite forallb_forall in Hl.
apply Forall_forall. intros [r e] Hin. pose proof (Hl _ Hin) as Hb. cbn [fst snd] in *.
apply sv_eqb_eq in Hb. rewrite (st_ok_restrict_reg tfibsegs H E ss ms' r HS), Hb. reflexivity.
Qed.
(* the live blocks' request sum is rd_sum of ablocks (lib/B/Prog/FSW_grow_holds.v grow_bb, copied: that file is not
   a dependency of this one) *)
Lemma piv_bb : forall B ly S, blocks_bytes S = rd_sum (ablocks B ly S).
Proof.
intros B ly S. unfold blocks_bytes, rd_sum, ablocks, blocks.
induction (st_chunks S) as [|c cs IH]; [reflexivity|].
cbn [List.filter fold_right]. destruct (is_alloc c); cbn [map fold_right snd]; rewrite IH; reflexivity.
Qed.
Lemma piv_req : forall k, 0 <= k -> req_size (k + HEAD) = k + HEAD.
Proof. intros k Hk. unfold req_size, HEAD. destruct (Z.eqb_spec (k + 16) 0); lia. Qed.
Lemma piv_word_eq : forall (m m' : word -> option byte) (P : Z -> Prop) (x : word),
  (forall z, P z -> m' (Z_to_bv 64 z) = m (Z_to_bv 64 z)) -> P (bv_unsigned x) -> m' x = m x.
Proof. intros m m' P x H Hp. rewrite <- (Z_to_bv_bv_unsigned 64 x). exact (H _ Hp). Qed.
(* sums over a permutation, and over the ASan blocks of a reader list *)
Lemma piv_rd_sum_perm : forall a b, Permutation a b -> rd_sum a = rd_sum b.
Proof. intros a b HP. induction HP; unfold rd_sum in *; cbn [fold_right] in *; lia. Qed.
Lemma piv_rd_sum_hb : forall L, rd_sum (rd_hblocks L) = rd_sum L + HEAD * Z.of_nat (length L).
Proof.
induction L as [|[a kk] L IH]; [reflexivity|]. unfold rd_sum, rd_hblocks in *. cbn [map fold_right fst snd length] in *.
rewrite IH. lia.
Qed.
(* the frame chain at q across a memory change off [q, q + 24), reads bounded by the stack top *)
Lemma piv_fpchain_kept : forall (l1 l2 : Z -> option Z) qq s top cl bp,
  fpchain l1 bp top cl -> (bp = qq \/ qq + 40 <= bp) -> s + 16 <= bp -> bp < top ->
  Forall (fun r => bad_next (fst (fst r)) top (snd r) = true \/ qq + 40 <= snd r) cl ->
  (forall a, s <= a -> a + 8 <= top -> a + 8 <= qq \/ qq + 24 <= a -> l2 a = l1 a) -> fpchain l2 bp top cl.
Proof.
intros l1 l2 qq s top cl. induction cl as [|[[fp ra] nfp] cl IH]; intros bp H Hq Hb Ht HF Hl; cbn [fpchain] in *.
- destruct H as (r & Hr & Hr2). exists r. rewrite Hl by lia. split; assumption.
- destruct H as (E & H8 & Hra & Hnfp & H4 & Hrest). subst fp.
  inversion HF as [|? ? Hr HF']; subst. cbn [fst snd] in Hr.
  split; [reflexivity|]. split; [exact H8|]. split; [rewrite Hl by lia; exact Hra|].
  split; [rewrite Hl by lia; exact Hnfp|]. split; [exact H4|].
  destruct (bad_next bp top nfp) eqn:Eb; [exact Hrest|].
  assert (Hn : bp < nfp /\ nfp < top - 16).
  { unfold bad_next in Eb. apply orb_false_iff in Eb as [Eb _]. apply orb_false_iff in Eb as [Eb1 Eb2].
    apply Z.leb_gt in Eb1. apply Z.leb_gt in Eb2. lia. }
  apply (IH nfp Hrest); [| lia | lia | exact HF' | exact Hl].
  destruct Hr as [Hr | Hr]; [exfalso; congruence | right; exact Hr].
Qed.
Lemma piv_chain_kept : forall (ly1 ly2 : alayout) (rd1 rd2 : reader) s qq top chq,
  achain ly1 rd1 s qq chq -> Forall (fun r => bad_next (fst (fst r)) top (snd r) = true \/ qq + 40 <= snd r) chq ->
  ly_top ly1 = top -> ly_top ly2 = top ->
  (forall a, s <= a < top -> ~ (qq <= a < qq + 24) -> rd2 a = rd1 a) -> achain ly2 rd2 s qq chq.
Proof.
intros ly1 ly2 rd1 rd2 s qq top chq H HF E1 E2 Hrd. unfold achain in *. rewrite E2. rewrite E1 in H.
destruct H as [H | (H1 & H2 & H3 & H4 & H5)]; [left; exact H|]. right.
split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [|exact H5].
apply (piv_fpchain_kept (rdword rd1) (rdword rd2) qq s top chq qq H4 (or_introl eq_refl) H1 ltac:(lia) HF).
intros a Ha Htp Hout. apply rdword_ext. intros j Hj. apply Hrd; lia.
Qed.
(* the members' own facts (FS_DOC_STRS, well-formedness, depth) *)
Lemma piv_mem_facts_gen : forall d l, FSDocStrs.fs_doc_values (PjTree.JObj l) ->
  FSDocStrs.fs_doc_strings (PjTree.JObj l) ->
  PjRoundTrip.pj_wf ReaderRes.jr_strtod (PjTree.JObj l) -> (PjTree.depth (PjTree.JObj l) <= Datatypes.S d)%nat ->
  forall dn kk x rm, l = dn ++ (kk, x) :: rm ->
  plain_bytes kk /\ (forall y, In y (x :: FSDocStrs.jv_vals x) -> FSDocStrs.str_or_obj y) /\
  FSDocStrs.fs_doc_strings x /\ PjRoundTrip.pj_wf ReaderRes.jr_strtod x /\ (PjTree.depth x <= d)%nat.
Proof.
intros d l HV HS HF HD dn. revert l HV HS HF HD.
induction dn as [|[k0 x0] dn IH]; intros l HV HS HF HD kk x rm El; subst l; cbn [app] in *.
- destruct (pim_vals_cons kk x rm HV) as (V1 & _). destruct (pim_strs_cons kk x rm HS) as (S1 & S2 & _).
  destruct (pim_wf_cons kk x rm HF) as (F1 & _). destruct (pim_depth_cons kk x rm d HD) as (D1 & _).
  repeat split; assumption.
- destruct (pim_vals_cons k0 x0 _ HV) as (_ & V2). destruct (pim_strs_cons k0 x0 _ HS) as (_ & _ & S3).
  destruct (pim_wf_cons k0 x0 _ HF) as (_ & F2). destruct (pim_depth_cons k0 x0 _ d HD) as (_ & D2).
  exact (IH _ V2 S3 F2 D2 kk x rm eq_refl).
Qed.
(* the shadow cell of an atom's address, as a denotation *)
Lemma piv_shx_denot : forall E n a c, ew E n = Z_to_bv 64 a -> ew E 32 = Z_to_bv 64 SHADOW_OFF ->
  0 <= a -> 0 <= c -> a + c < 2 ^ 47 -> sv_denot E (pi_shx n c) = Z_to_bv 64 (pi_sh (a + c)).
Proof.
intros E n a c Hn H32 Ha Hc Hac. apply bv_eq. change (bv_unsigned (sv_denot E (pi_shx n c))) with (YP0e.U E (pi_shx n c)).
unfold pi_shx. rewrite (pi_U_shadow E n c a Hn Ha Hc Hac H32). rewrite unsigned_lit_small; [reflexivity|].
unfold pi_sh, SHADOW_OFF. split; [pose proof (Z.div_pos (a + c) 8 ltac:(lia) ltac:(lia)); lia|].
pose proof (Z.div_le_upper_bound (a + c) 8 (2 ^ 44) ltac:(lia) ltac:(lia)). lia.
Qed.
Lemma piv_den_off : forall E n z c, ew E n = Z_to_bv 64 z -> 0 <= z -> 0 <= c -> z + c < 2 ^ 64 ->
  sv_denot E (SOff n c) = Z_to_bv 64 (z + c).
Proof.
intros E n z c Hn Hz Hc Hzc. apply bv_eq. rewrite denot_SOff, Hn, (unsigned_lit_small z) by lia.
rewrite (unsigned_lit_small (z + c)) by lia. apply zcanon_id. unfold M64. lia.
Qed.
(* the frame chunks of the member loop (pib_csL) from pib_frameL, under any env holding q (9), v (19), the shadow
   base (32) and the saved registers at xatom 3 .. 15 *)
Lemma piv_cs_ok : forall E m sp xr0, length xr0 = 13%nat ->
  (forall j, (j < 13)%nat -> ew E (xatom (3 + j)) = nth j xr0 (Z_to_bv 64 0)) ->
  pib_frame0 m sp xr0 -> Forall (YP09.chunk_ok tfibsegs E m (sp - 144)) pi_cs.
Proof.
intros E m sp xr0 Hl HX HF. unfold pib_frame0 in HF. rewrite Forall_forall in HF.
assert (HF' : forall j, (j < 13)%nat ->
  val_mem tfibsegs m (sp - 144 + (136 - 8 * Z.of_nat j)) 8 (bv_unsigned (nth j xr0 (Z_to_bv 64 0)))).
{ intros j Hj. replace (sp - 144 + (136 - 8 * Z.of_nat j)) with (sp - 8 - 8 * Z.of_nat j) by lia.
  apply HF. apply in_seq. lia. }
unfold pi_cs.
repeat (apply Forall_cons; [
  lazymatch goal with |- YP09.chunk_ok _ _ _ _ (YP09.mkChunk ?off (CVal 8 (SOff (xatom ?jj) 0))) =>
    let i := eval vm_compute in (jj - 3)%nat in
    apply (chunk_ok_val tfibsegs _ _ _ off 8 _ (bv_unsigned (nth i xr0 (Z_to_bv 64 0))));
    [ rewrite fsw_SOff0; change jj with (3 + i)%nat; rewrite (HX i ltac:(lia)); symmetry; apply Z_to_bv_bv_unsigned
    | apply u64_range | cbn; lia
    | let H := fresh in pose proof (HF' i ltac:(lia)) as H; cbn [Z.of_nat Pos.of_succ_nat] in H;
      replace (sp - 144 + off) with (sp - 144 + (136 - 8 * Z.of_nat i)) by (cbn; lia); exact H ] end|]).
apply Forall_nil.
Qed.
Lemma piv_csL_ok : forall E m sp xr0 q0 v0, length xr0 = 13%nat ->
  (forall j, (j < 13)%nat -> ew E (xatom (3 + j)) = nth j xr0 (Z_to_bv 64 0)) ->
  ew E 9 = Z_to_bv 64 q0 -> ew E 19 = Z_to_bv 64 v0 -> ew E 32 = Z_to_bv 64 SHADOW_OFF ->
  0 <= q0 -> 0 <= v0 -> v0 + 56 < 2 ^ 47 ->
  pib_frameL m sp xr0 q0 v0 -> Forall (YP09.chunk_ok tfibsegs E m (sp - 144)) pib_csL.
Proof.
intros E m sp xr0 q0 v0 Hl HX E9 E19 E32 Hq0 Hv0 Hv1 (HF0 & F0 & F8 & F16 & F24 & F32).
unfold pib_csL. apply Forall_app. split; [|exact (piv_cs_ok E m sp xr0 Hl HX HF0)].
assert (Hsh : forall y, 0 <= y < 2 ^ 47 -> 0 <= pi_sh y < 2 ^ 64).
{ intros y Hy. unfold pi_sh, SHADOW_OFF. split; [pose proof (Z.div_pos y 8 ltac:(lia) ltac:(lia)); lia|].
  pose proof (Z.div_le_upper_bound y 8 (2 ^ 44) ltac:(lia) ltac:(lia)). lia. }
repeat apply Forall_cons; try apply Forall_nil.
- apply (chunk_ok_val tfibsegs E m (sp - 144) 0 8 (SLit 1152921504606846976) 1152921504606846976);
    [reflexivity | cbn; lia | cbn; lia | rewrite Z.add_0_r; exact F0].
- apply (chunk_ok_val tfibsegs E m (sp - 144) 8 8 (pi_shx 19 32) (pi_sh (v0 + 32)));
    [apply piv_shx_denot; [exact E19 | exact E32 | lia | lia | lia]
    | cbn; pose proof (Hsh (v0 + 32) ltac:(lia)); lia | cbn; lia
    | replace (sp - 144 + 8) with (sp - 136) by lia; exact F8].
- apply (chunk_ok_val tfibsegs E m (sp - 144) 16 8 (SOff 19 32) (v0 + 32));
    [apply piv_den_off; [exact E19 | lia | lia | lia] | cbn; lia | cbn; lia
    | replace (sp - 144 + 16) with (sp - 128) by lia; exact F16].
- apply (chunk_ok_val tfibsegs E m (sp - 144) 24 8 (pi_shx 19 24) (pi_sh (v0 + 24)));
    [apply piv_shx_denot; [exact E19 | exact E32 | lia | lia | lia]
    | cbn; pose proof (Hsh (v0 + 24) ltac:(lia)); lia | cbn; lia
    | replace (sp - 144 + 24) with (sp - 120) by lia; exact F24].
- apply (chunk_ok_val tfibsegs E m (sp - 144) 32 8 (SOff 19 24) (v0 + 24));
    [apply piv_den_off; [exact E19 | lia | lia | lia] | cbn; lia | cbn; lia
    | replace (sp - 144 + 32) with (sp - 112) by lia; exact F32].
Qed.
(* ... and back: pib_frameL read off a frame region whose chunks include pib_csL *)
Lemma piv_frameL_of : forall E m sp xr0 q0 v0 cs', length xr0 = 13%nat ->
  bv_unsigned (ew E 2) = sp - 144 -> ew E 9 = Z_to_bv 64 q0 -> ew E 19 = Z_to_bv 64 v0 ->
  ew E 32 = Z_to_bv 64 SHADOW_OFF -> (forall j, (j < 13)%nat -> ew E (xatom (3 + j)) = nth j xr0 (Z_to_bv 64 0)) ->
  0 <= v0 -> v0 + 56 < 2 ^ 47 ->
  region_ok tfibsegs E m (YP09.mkRegion (Some 2%nat) 0 144 0 0 cs') -> incl pib_csL cs' ->
  pib_frameL m sp xr0 q0 v0.
Proof.
intros E m sp xr0 q0 v0 cs' Hl E2 E9 E19 E32 EX Hv0 Hv1 HR Hinc.
pose proof (bv_unsigned_in_range 64 (ew E 2)) as Hsp. unfold bv_modulus in Hsp. change (2 ^ Z.of_N 64) with (2 ^ 64) in Hsp.
assert (F : forall off e x, In (YP09.mkChunk off (CVal 8 e)) pib_csL -> sv_denot E e = Z_to_bv 64 x ->
  0 <= x < 2 ^ 64 -> val_mem tfibsegs m (sp - 144 + off) 8 x).
{ intros off e x Hin He Hx. exact (fsw_field E m 2 (sp - 144) cs' 0 144 0 0 off 8 e x HR E2 (Hinc _ Hin) He
    ltac:(cbn; lia) ltac:(cbn; lia)). }
assert (Hsh : forall y, 0 <= y < 2 ^ 47 -> 0 <= pi_sh y < 2 ^ 64).
{ intros y Hy. unfold pi_sh, SHADOW_OFF. split; [pose proof (Z.div_pos y 8 ltac:(lia) ltac:(lia)); lia|].
  pose proof (Z.div_le_upper_bound y 8 (2 ^ 44) ltac:(lia) ltac:(lia)). lia. }
split.
- unfold pib_frame0. apply Forall_forall. intros j Hj. apply in_seq in Hj.
  replace (sp - 8 - 8 * Z.of_nat j) with (sp - 144 + (136 - 8 * Z.of_nat j)) by lia.
  apply (F _ (SOff (xatom (3 + j)) 0)); [| rewrite fsw_SOff0, EX by lia; symmetry; apply Z_to_bv_bv_unsigned
    | apply u64_range].
  unfold pib_csL. apply in_or_app. right. unfold pi_cs.
  destruct Hj as [_ Hj]. cbn [Nat.add] in Hj.
  do 13 (destruct j as [|j]; [cbn; tauto|]). lia.
- split; [replace (sp - 144) with (sp - 144 + 0) at 1 by lia; apply (F 0 (SLit 1152921504606846976));
    [cbn; tauto | reflexivity | lia]|].
  split; [replace (sp - 136) with (sp - 144 + 8) by lia; apply (F 8 (pi_shx 19 32));
    [cbn; tauto | apply piv_shx_denot; [exact E19 | exact E32 | lia | lia | lia] | apply Hsh; lia]|].
  split; [replace (sp - 128) with (sp - 144 + 16) by lia; apply (F 16 (SOff 19 32));
    [cbn; tauto | apply piv_den_off; [exact E19 | lia | lia | lia] | lia]|].
  split; [replace (sp - 120) with (sp - 144 + 24) by lia; apply (F 24 (pi_shx 19 24));
    [cbn; tauto | apply piv_shx_denot; [exact E19 | exact E32 | lia | lia | lia] | apply Hsh; lia]|].
  replace (sp - 112) with (sp - 144 + 32) by lia; apply (F 32 (SOff 19 24));
    [cbn; tauto | apply piv_den_off; [exact E19 | lia | lia | lia] | lia].
Qed.

End F.

(* ================= parse_items_spec k's entry: the Section of every step below ================= *)
Section V. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Variables (k : nat) (ly : alayout) (S : astate) (U : list (Z * Z)) (W : world tfibsegs) (regs : bvmap 5 word)
  (mem : word -> option byte) (md : Model) (q ot v text len p tcap : Z) (tb : list byte)
  (ms : list (list Z * PjTree.jv)) (pr : bool) (rest : list Z) (live peak cnt fail : Z).
Let sp0 : Z := spZ regs.
Let dd : Z := Z.of_nat k.
Let FP : list (Z * Z) := [(v, v + 56)] ++ FS_PSTAT_FP.
Let STKt : Z := STK_parse_items (1 - k) + (ot - sp0).
Let xr : list word := map (YK11.getr regs) pi_saved_regs.
Variable ch : list (Z * Z * Z).
Hypothesis Hk : (k <= 1)%nat.
Hypothesis HSS : FsShadowSyms B.
Hypothesis HPRE : fpreU tfibsegs B (STK_parse_items (1 - k)) ly S U W regs mem md ch.
Hypothesis HHEADS : FSupoisonU.fs_heads B ly S U.
Hypothesis HWIN : rd_win tfibsegs regs ly W mem q ot.
Hypothesis HQ16 : spZ regs + 16 <= q.
Hypothesis HTX : rd_text tfibsegs B ly S W mem text len tcap.
Hypothesis HIN0 : PjIn.pj_in_ok tfibsegs (rdW W mem) q text len p dd tb.
Hypothesis HVTX : v + 56 <= text - HEAD \/ text + tcap <= v.
Hypothesis HPO0 : pobj tfibsegs B ly S W mem v.
Hypothesis HQT : quiet cnt fail (Z.of_nat (length (PjRoundTrip.ttrace (PjTree.JObj ms)))).
Hypothesis HSZ : rd_sizes_ok (PjRoundTrip.ttrace (PjTree.JObj ms)).
Hypothesis HLIVE : live + rd_live (PjRoundTrip.ttrace (PjTree.JObj ms)) < 2 ^ 64.
Hypothesis HEV : st_nev S + rd_ev (PjRoundTrip.ttrace (PjTree.JObj ms)) <= EV_MAX.
Hypothesis HBB : blocks_bytes S + rd_live (PjRoundTrip.ttrace (PjTree.JObj ms)) <= LIVE_MAX.
Hypothesis HFRL : Z.of_nat (length (frames S)) <= FRL_parse_value (Z.of_nat k + 1).
Hypothesis H10 : YK11.getr regs 10 = w64 q.
Hypothesis H11 : YK11.getr regs 11 = w64 v.
Hypothesis H12 : YK11.getr regs 12 = w64 1.
Hypothesis HCH0 : exists chq, achain ly (aview tfibsegs (w_H W) (unpoison U mem)) (spZ regs) q chq /\
  Forall (fun r => bad_next (fst (fst r)) (ly_top ly) (snd r) = true \/ q + 40 <= snd r) chq.
Hypothesis HREST : ReaderRes.rest_at tb text p = concat (WriterValue.wvpieces (PjTree.JObj ms) pr (Z.of_nat k)) ++ rest.
Hypothesis HDV : FSDocStrs.fs_doc_values (PjTree.JObj ms).
Hypothesis HDS : FSDocStrs.fs_doc_strings (PjTree.JObj ms).
Hypothesis HWF : PjRoundTrip.pj_wf ReaderRes.jr_strtod (PjTree.JObj ms).
Hypothesis HDEP : (PjTree.depth (PjTree.JObj ms) <= 2 - k)%nat.
Hypothesis HZERO : PjStruct.pj_zero tfibsegs (rdW W mem) v.
Hypothesis HVSP : v + 56 <= spZ regs - STK_parse_items (1 - k) \/ ot <= v.
Hypothesis HGLOB : fs_glob tfibsegs W mem live peak cnt fail.

(* ================= small facts of the entry ================= *)
Lemma piv_sp0 : sp0 mod 16 = 0 /\ alloc_ceiling + STK_parse_items (1 - k) <= sp0 /\ sp0 <= 2 ^ 47.
Proof.
pose proof (fsw_sp B _ ly S U W regs mem md ch (proj1 HPRE)) as (H1 & H2 & H3 & _). unfold sp0. lia.
Qed.
Lemma piv_stk144 : 144 <= STK_parse_items (1 - k).
Proof.
assert (HF : FRAME_parse_items <= STK_parse_items (1 - k))
  by (unfold STK_parse_items, STK_parse_items_of, zmaxl; cbn [fold_right]; lia).
change FRAME_parse_items with 144 in HF. exact HF.
Qed.
Lemma piv_xr_len : length xr = 13%nat.
Proof. unfold xr. rewrite length_map. reflexivity. Qed.
Lemma piv_v_rng : 4096 <= v /\ v + 56 <= alloc_ceiling.
Proof.
pose proof HPRE as ((HAP & _ & _) & _). pose proof HAP as (HAR & _).
exact (fsw_pobj_low B ly S W (unpoison U mem) md mem v HAR HPO0).
Qed.
(* the entry's stack bounds around q *)
Lemma piv_q_stack : ly_stk_lo ly <= q /\ q + 24 <= ly_stk_hi ly /\ q mod 8 = 0 /\ alloc_ceiling <= q /\
  q + 24 <= 2 ^ 47.
Proof.
pose proof HPRE as ((HAP & _ & _) & _). pose proof HAP as (_ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _ & Htop & Htop2).
pose proof HWIN as (Hsq & Hq24 & _ & Hotly & _).
pose proof piv_sp0 as (_ & HceilS & _). pose proof piv_stk144.
pose proof (PjIn.pj_in_ok_bounds tfibsegs _ _ _ _ _ _ _ HIN0) as (_ & _ & _ & _ & _ & _ & _ & Hq8 & _).
lia.
Qed.

(* ================= the resume env of a call ================= *)
Lemma piv_env_at : forall regsC regs' xs R, pib_regsP B regs q v regsC R -> aregs_preserved regsC regs' ->
  ew (Ereg regs' (fs_extraT ++ xs)) 9 = Z_to_bv 64 q /\ ew (Ereg regs' (fs_extraT ++ xs)) 19 = Z_to_bv 64 v /\
  ew (Ereg regs' (fs_extraT ++ xs)) 32 = Z_to_bv 64 SHADOW_OFF /\
  bv_unsigned (ew (Ereg regs' (fs_extraT ++ xs)) 2) = sp0 - 144 /\
  ew (Ereg regs' (fs_extraT ++ xs)) 3 = Z_to_bv 64 (as_gp B) /\ ew (Ereg regs' (fs_extraT ++ xs)) 4 = Z_to_bv 64 (as_tp B).
Proof.
intros regsC regs' xs R (Rsp & R9 & R19 & R3 & R4 & _) HP.
rewrite (ew_Ereg_nat regs' _ 9 9%bv eq_refl), (ew_Ereg_nat regs' _ 19 19%bv eq_refl),
  (ew_Ereg_nat regs' _ 2 2%bv eq_refl), (ew_Ereg_nat regs' _ 3 3%bv eq_refl), (ew_Ereg_nat regs' _ 4 4%bv eq_refl).
change 32%nat with (32 + 0)%nat. rewrite ew_Ereg_extra. cbn [nth fs_extraT app].
rewrite (fsw_pres regsC regs' 9%bv HP ltac:(piv_acs)), (fsw_pres regsC regs' 19%bv HP ltac:(piv_acs)),
  (fsw_pres regsC regs' 2%bv HP ltac:(piv_acs)), (fsw_pres regsC regs' 3%bv HP ltac:(piv_acs)),
  (fsw_pres regsC regs' 4%bv HP ltac:(piv_acs)).
unfold spZ in Rsp. unfold sp0, spZ. repeat split; assumption.
Qed.
Lemma piv_setr_ok : forall regsC regs' xs R e10, pib_regsP B regs q v regsC R -> aregs_preserved regsC regs' ->
  piv_R_ok R = true ->
  YK11.getr regs' 10 = sv_denot (Ereg regs' (fs_extraT ++ xs)) e10 ->
  Forall (fun r => fst r <> 0%bv /\ YK11.getr regs' (fst r) = sv_denot (Ereg regs' (fs_extraT ++ xs)) (snd r))
    ((10%bv, e10) :: R).
Proof.
intros regsC regs' xs R e10 HR HP Hok Ha0.
pose proof (piv_env_at regsC regs' xs R HR HP) as (E9 & E19 & E32 & _).
pose proof HR as (_ & R9 & R19 & _ & _ & RL).
constructor; [split; [intros E; discriminate E | exact Ha0]|].
unfold piv_R_ok in Hok. rewrite forallb_forall in Hok. rewrite Forall_forall in RL |- *.
intros [r e] Hin. pose proof (Hok _ Hin) as Hb. pose proof (RL _ Hin) as Hr. cbn [fst snd] in *.
apply andb_prop in Hb as [Hb Hat]. apply andb_prop in Hb as [Hb Hcs]. apply andb_prop in Hb as [H0 _].
split.
- intros ->. discriminate H0.
- rewrite (fsw_pres regsC regs' r HP).
  + rewrite Hr. apply pik_sv_denot_agree; [reflexivity|].
    intros n Hn. rewrite forallb_forall in Hat. pose proof (Hat n Hn) as Hn'.
    apply orb_prop in Hn' as [Hn'|Hn']; [apply orb_prop in Hn' as [Hn'|Hn']|]; apply Nat.eqb_eq in Hn'; subst n.
    * rewrite (ew_Ereg_nat regsC _ 9 9%bv eq_refl), R9. symmetry. exact E9.
    * rewrite (ew_Ereg_nat regsC _ 19 19%bv eq_refl), R19. symmetry. exact E19.
    * change 32%nat with (32 + 0)%nat. rewrite ew_Ereg_extra. cbn [nth fs_extraT app].
      rewrite <- E32. change 32%nat with (32 + 0)%nat. rewrite ew_Ereg_extra. reflexivity.
  + unfold acallee_saved. apply orb_prop in Hcs as [Hcs|Hcs]; [apply orb_prop in Hcs as [Hcs|Hcs]|].
    * apply Z.eqb_eq in Hcs. lia.
    * apply Z.eqb_eq in Hcs. lia.
    * apply andb_prop in Hcs as [Hc1 Hc2]. apply Z.leb_le in Hc1. apply Z.leb_le in Hc2. lia.
Qed.

(* ================= the call premises every step needs ================= *)
(* where the text and in->p lie *)
Lemma piv_text_rng : forall lyc Sc (W1 : world tfibsegs) mx mdx memC pc d,
  AR tfibsegs B lyc Sc W1 mx mdx -> rd_text tfibsegs B lyc Sc W1 memC text len tcap ->
  PjIn.pj_in_ok tfibsegs (rdW W1 memC) q text len pc d tb ->
  4096 + HEAD <= text /\ text <= pc <= text + len /\ text + len < text + tcap /\ text + tcap <= alloc_ceiling /\
  alloc_ceiling <= 2 ^ 47 - 2 ^ 23.
Proof.
intros lyc Sc W1 mx mdx memC pc d HAR (Ht & Hb & Hl) HIN.
destruct (fsw_rblock_low B lyc Sc W1 mx mdx _ text tcap HAR Hb) as (_ & H2).
pose proof (PjIn.pj_in_ok_bounds tfibsegs _ _ _ _ _ _ _ HIN) as (_ & _ & _ & Hp & _).
pose proof asan_consts as (C1 & _). lia.
Qed.
(* a live-list sum is non-negative *)
Lemma piv_rd_sum_nn : forall lyc Sc (W1 : world tfibsegs) memC L, rd_blocks_ok tfibsegs B lyc Sc W1 memC L ->
  0 <= rd_sum L.
Proof.
intros lyc Sc W1 memC L. induction L as [|[a kk] L IH]; intros H; [unfold rd_sum; cbn; lia|].
unfold rd_sum in *. cbn [fold_right fst snd].
assert (Hkk : 0 < kk) by (destruct (H a kk (or_introl eq_refl)) as (_ & _ & Hk0 & _); exact Hk0).
assert (HL : rd_blocks_ok tfibsegs B lyc Sc W1 memC L) by (intros a' k' Hin; apply H; right; exact Hin).
pose proof (IH HL). lia.
Qed.
(* the live list's blocks are none of the entry's *)
Lemma piv_not_entry : forall lyc Sc (W1 : world tfibsegs) mx mdx L, AR tfibsegs B lyc Sc W1 mx mdx ->
  Permutation (ablocks B lyc Sc) (ablocks B ly S ++ rd_hblocks L) ->
  forall b, In b (rd_hblocks L) -> ~ In b (ablocks B ly S).
Proof.
intros lyc Sc W1 mx mdx L HAR HP b Hb He.
pose proof (FSW_pj_set_heads.pSh_ablocks_nodup B lyc Sc W1 mx mdx HAR) as ND.
apply (Permutation_NoDup HP) in ND. apply (proj2 (NoDup_ListNoDup _)) in ND.
exact (parse_items_shape.pis_nodup_app_disj _ _ _ _ ND He Hb).
Qed.
(* the budget premises of a callee whose events X come next in the trace: tr = T ++ X ++ Y *)
Lemma piv_budget : forall lyc Sc L T X Y,
  PjRoundTrip.ttrace (PjTree.JObj ms) = T ++ X ++ Y ->
  st_nev Sc <= st_nev S + rd_ev T ->
  Permutation (ablocks B lyc Sc) (ablocks B ly S ++ rd_hblocks L) ->
  rd_sum L = PjGrammar.held T -> (length L <= length T)%nat ->
  quiet (cnt + Z.of_nat (length T)) fail (Z.of_nat (length X)) /\
  live + PjGrammar.held T + rd_live X < 2 ^ 64 /\
  st_nev Sc + rd_ev X <= EV_MAX /\ blocks_bytes Sc + rd_live X <= LIVE_MAX /\ rd_sizes_ok X.
Proof.
intros lyc Sc L T X Y Htr Hnev HP HS HL.
pose proof HQT as HQT'. pose proof HSZ as HSZ'. pose proof HLIVE as HLIVE'. pose proof HEV as HEV'.
pose proof HBB as HBB'.
rewrite Htr in HQT', HSZ', HLIVE', HEV', HBB'.
rewrite !length_app, !Nat2Z.inj_add in HQT'.
apply pim_sizes_app in HSZ' as [_ HSZ']. apply pim_sizes_app in HSZ' as [HSZ' _].
rewrite !pim_rd_live_app in HLIVE', HBB'. rewrite !pim_rd_ev_app in HEV'.
pose proof (pim_held_live T) as HHL. pose proof (pim_D_live L T HS HL) as HDL.
pose proof (pim_rd_live_nn Y) as HY1. pose proof (pim_rd_ev_nn Y) as HY2.
assert (BBe : blocks_bytes Sc = blocks_bytes S + rd_sum L + HEAD * Z.of_nat (length L)).
{ rewrite (piv_bb B lyc Sc), (piv_bb B ly S), (piv_rd_sum_perm _ _ HP),
    pim_rd_sum_app, piv_rd_sum_hb. lia. }
split; [|split; [unfold HEAD in *; lia|split; [lia|split; [unfold HEAD in *; lia | exact HSZ']]]].
destruct (pim_quiet_split cnt fail (Z.of_nat (length T)) (Z.of_nat (length X) + Z.of_nat (length Y))
  ltac:(lia) ltac:(lia) HQT') as [_ HQ2].
destruct (pim_quiet_split (cnt + Z.of_nat (length T)) fail (Z.of_nat (length X)) (Z.of_nat (length Y))
  ltac:(lia) ltac:(lia) HQ2) as [HQ3 _].
exact HQ3.
Qed.
(* the text bytes at in->p, read off pj_in_ok's `bytes_at text tb` and the split of rest_at *)
Lemma piv_txt_bytes : forall m qq pc d bs more, PjIn.pj_in_ok tfibsegs m qq text len pc d tb ->
  ReaderRes.rest_at tb text pc = bs ++ more ->
  Forall (fun c => 0 <= c < 256) bs /\
  (forall i, (i < length bs)%nat -> mbyte tfibsegs m (pc + Z.of_nat i) = Some (Z_to_bv 8 (nth i bs 0))).
Proof.
intros m qq pc d bs more HIN HR.
pose proof (PjIn.pj_in_ok_bounds tfibsegs _ _ _ _ _ _ _ HIN) as (_ & _ & _ & Hp & _).
pose proof HIN as (_ & _ & _ & _ & _ & _ & _ & _ & _ & (Bt0 & Bt1 & Bt) & _).
assert (KEY : forall i, (i < length bs)%nat -> exists b : byte, mbyte tfibsegs m (pc + Z.of_nat i) = Some b /\
  bv_unsigned b = nth i bs 0).
{ intros i Hi.
  assert (E : nth_error (ReaderRes.rest_at tb text pc) i = Some (nth i bs 0))
    by (rewrite HR, nth_error_app1 by exact Hi; apply nth_error_nth'; exact Hi).
  unfold ReaderRes.rest_at, ReaderRes.zb in E. rewrite nth_error_map, nth_error_skipn in E.
  destruct (nth_error tb (Z.to_nat (pc - text) + i)) as [b|] eqn:Eb; cbn in E; [|discriminate].
  injection E as E. exists b. split; [|exact E].
  assert (Hj : (Z.to_nat (pc - text) + i < length tb)%nat) by (apply nth_error_Some; rewrite Eb; discriminate).
  pose proof (Bt _ Hj) as Hb. rewrite Eb in Hb.
  replace (text + Z.of_nat (Z.to_nat (pc - text) + i)) with (pc + Z.of_nat i) in Hb by lia. exact Hb. }
split.
- apply Forall_forall. intros c Hc. apply (In_nth bs c 0) in Hc as (i & Hi & <-).
  destruct (KEY i Hi) as (b & _ & Eb). rewrite <- Eb. pose proof (bv_unsigned_in_range 8 b) as Hr.
  unfold bv_modulus in Hr. change (2 ^ Z.of_N 8) with 256 in Hr. lia.
- intros i Hi. destruct (KEY i Hi) as (b & Hm & Eb). rewrite Hm, <- Eb, Z_to_bv_bv_unsigned. reflexivity.
Qed.

(* ================= the shadow entries of a member-loop run ================= *)
(* q's 24 bytes: the stack's zero shadow *)
Lemma piv_sh_q : forall lyc Sc Uc (W1 : world tfibsegs) mem1 md1 E (b : nat),
  ARU tfibsegs B lyc Sc Uc W1 mem1 md1 -> ly_stk_lo lyc = ly_stk_lo ly -> ly_stk_hi lyc = ly_stk_hi ly ->
  YP0e.U E fs_Bx = SHADOW_OFF -> YP0e.U E (SOff b 0) = q ->
  shent_ok tfibsegs fs_Bx E (rdW W1 mem1) (mkSHE b 0 24).
Proof.
intros lyc Sc Uc W1 mem1 md1 E b HARU Hlo Hhi UB Uq.
pose proof piv_q_stack as (Hqlo & Hqhi & Hq8 & Hqc & Hq47). pose proof asan_consts as (C1 & _).
pose proof HARU as (HAR & _).
apply (shent_ok_of_range tfibsegs (w_H W1) mem1 E fs_Bx b q 24 q 0 24);
  [ apply (proj1 (fsw_ARU_stack_ra tfibsegs B (AR_laws_ok tfibsegs B) lyc Sc Uc W1 mem1 md1 (w_H W1) q 24 HARU
      ltac:(lia) ltac:(lia)));
    exact (pi_RA_stack B lyc Sc W1 (unpoison Uc mem1) md1 q 24 HAR ltac:(lia) ltac:(lia) Hq8 ltac:(reflexivity) ltac:(lia))
  | exact UB | exact Uq | lia | lia |].
intros x Hx. cbn [Z.min Z.max] in Hx. unfold SHADOW_OFF in *. lia.
Qed.
(* v's 56 bytes: pobj's range_addressable, off the shadow band *)
Lemma piv_sh_v : forall lyc Sc Uc (W1 : world tfibsegs) mem1 md1 E (b : nat),
  ARU tfibsegs B lyc Sc Uc W1 mem1 md1 -> pobj tfibsegs B lyc Sc W1 mem1 v ->
  YP0e.U E fs_Bx = SHADOW_OFF -> YP0e.U E (SOff b 0) = v ->
  shent_ok tfibsegs fs_Bx E (rdW W1 mem1) (mkSHE b 0 56).
Proof.
intros lyc Sc Uc W1 mem1 md1 E b HARU HPO UB Uv. pose proof HARU as (HAR & _).
apply (shent_ok_of_range tfibsegs (w_H W1) mem1 E fs_Bx b v 56 v 0 56);
  [ destruct HPO as [[(_ & _ & Hr)|(_ & _ & Hr)] _]; exact Hr | exact UB | exact Uv | lia | lia |].
intros x Hx. cbn [Z.min Z.max] in Hx.
exact (fsw_pobj_off_shadow B lyc Sc W1 (unpoison Uc mem1) md1 mem1 v HAR HPO x ltac:(lia)).
Qed.
(* a window [z + lo, z + hi) of a live block's body (the text, a key slot): addressable, off the shadow band *)
Lemma piv_sh_blk : forall lyc Sc Uc (W1 : world tfibsegs) mem1 md1 E (b : nat) P nn z lo hi,
  ARU tfibsegs B lyc Sc Uc W1 mem1 md1 -> FSupoisonU.fs_heads B lyc Sc Uc ->
  In (P, nn) (ablocks B lyc Sc) -> P + HEAD <= z + lo -> lo <= hi -> z + hi <= P + nn ->
  YP0e.U E fs_Bx = SHADOW_OFF -> YP0e.U E (SOff b 0) = z ->
  shent_ok tfibsegs fs_Bx E (rdW W1 mem1) (mkSHE b lo hi).
Proof.
intros lyc Sc Uc W1 mem1 md1 E b P nn z lo hi HARU HHD Hin H1 H2 H3 UB Uz. pose proof HARU as (HAR & _).
destruct (fsw_ablock_low B lyc Sc W1 (unpoison Uc mem1) md1 P nn HAR Hin) as (L1 & L2 & L3).
apply (shent_ok_of_range tfibsegs (w_H W1) mem1 E fs_Bx b (z + lo) (hi - lo) z lo hi);
  [ apply (fsw_block_body_addressable B lyc Sc Uc W1 mem1 md1 P nn (z + lo) (hi - lo) HARU HHD Hin);
      unfold HEAD in *; lia
  | exact UB | exact Uz | lia | lia |].
intros x Hx. rewrite (Z.min_l lo hi H2), (Z.max_r lo hi H2) in Hx.
apply (fsw_ablock_off_shadow B lyc Sc W1 (unpoison Uc mem1) md1 P nn HAR Hin x). unfold HEAD in *. lia.
Qed.

(* ================= the members' facts, the window, the frames ================= *)
Lemma piv_mem_facts : forall dn kk x rm, ms = dn ++ (kk, x) :: rm ->
  plain_bytes kk /\ (forall y, In y (x :: FSDocStrs.jv_vals x) -> FSDocStrs.str_or_obj y) /\
  FSDocStrs.fs_doc_strings x /\ PjRoundTrip.pj_wf ReaderRes.jr_strtod x /\
  (PjTree.depth x <= 2 - Datatypes.S k)%nat.
Proof.
intros dn kk x rm E. apply (piv_mem_facts_gen (1 - k) ms HDV HDS HWF ltac:(lia) dn kk x rm E).
Qed.
(* the caller's window across two steps *)
Lemma piv_wkeep_trans : forall (W1 W2 : world tfibsegs) m1 m2 s,
  wkeep tfibsegs W W1 mem m1 sp0 ot q 24 -> wkeep tfibsegs W1 W2 m1 m2 s ot q 24 -> s <= sp0 ->
  wkeep tfibsegs W W2 mem m2 sp0 ot q 24.
Proof.
intros W1 W2 m1 m2 s HW1 HW2 Hs a Ha Hq.
destruct (HW1 a Ha Hq) as (B1 & R1). destruct (HW2 a ltac:(lia) Hq) as (B2 & R2).
split; [rewrite B2; exact B1 | rewrite R1; exact R2].
Qed.
(* the fake frames across the caller's journal (own = []) *)
Lemma piv_frames : forall lyc Sc Uc (W1 : world tfibsegs) memC mdC kc,
  pib_jc B k ly S U W regs mem md ot v lyc Sc Uc W1 memC mdC kc -> frames Sc = frames S.
Proof.
intros lyc Sc Uc W1 memC mdC kc (HJ & _). pose proof HJ as (_ & _ & _ & _ & _ & Hfr & _). exact Hfr.
Qed.

End V.

(* ================= slice M (pib_IM at __asan_memset -> pib_IV at parse_value): image-free helpers ============ *)
Section MH. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.

(* the resume env's extra words (FSW_parse_items_seg.pib_xsK) *)
Lemma pivm_xsK_nth : forall p e d xr kids keys n cap a klen, length xr = 13%nat ->
  nth 0 (pib_xsK p e d xr kids keys n cap a klen) (Z_to_bv 64 0) = Z_to_bv 64 p /\
  nth 1 (pib_xsK p e d xr kids keys n cap a klen) (Z_to_bv 64 0) = Z_to_bv 64 e /\
  nth 2 (pib_xsK p e d xr kids keys n cap a klen) (Z_to_bv 64 0) = Z_to_bv 64 d /\
  (forall j, (j < 13)%nat -> nth (3 + j) (pib_xsK p e d xr kids keys n cap a klen) (Z_to_bv 64 0) =
     nth j xr (Z_to_bv 64 0)) /\
  nth 16 (pib_xsK p e d xr kids keys n cap a klen) (Z_to_bv 64 0) = Z_to_bv 64 kids /\
  nth 17 (pib_xsK p e d xr kids keys n cap a klen) (Z_to_bv 64 0) = Z_to_bv 64 keys /\
  nth 18 (pib_xsK p e d xr kids keys n cap a klen) (Z_to_bv 64 0) = Z_to_bv 64 n /\
  nth 19 (pib_xsK p e d xr kids keys n cap a klen) (Z_to_bv 64 0) = Z_to_bv 64 cap /\
  nth 20 (pib_xsK p e d xr kids keys n cap a klen) (Z_to_bv 64 0) = Z_to_bv 64 a /\
  nth 21 (pib_xsK p e d xr kids keys n cap a klen) (Z_to_bv 64 0) = Z_to_bv 64 klen /\
  nth 23 (pib_xsK p e d xr kids keys n cap a klen) (Z_to_bv 64 0) = Z_to_bv 64 (kids + 56 * n).
Proof.
intros p e d xr kids keys n cap a klen Hl. unfold pib_xsK, pib_xs.
do 13 (destruct xr as [|? xr]; [discriminate Hl|]). destruct xr; [|discriminate Hl].
cbn [app nth]. repeat split; try reflexivity.
intros j Hj. do 13 (destruct j as [|j]; [reflexivity|]). lia.
Qed.

(* v's region pib_vR from v's header (A walk's pic_v_ok at atom 19) *)
Lemma pivm_vR_ok : forall E m v kids keys n cap,
  bv_unsigned (ew E 19) = v -> ew E (xatom 16) = Z_to_bv 64 kids -> ew E (xatom 17) = Z_to_bv 64 keys ->
  ew E (xatom 18) = Z_to_bv 64 n -> ew E (xatom 19) = Z_to_bv 64 cap ->
  0 <= v -> v + 56 <= 2 ^ 64 -> (forall i, 0 <= i < 56 -> writable_at tfibsegs m (v + i)) ->
  PjStruct.pj_hdr tfibsegs m v 6 0 0 kids keys n cap -> region_ok tfibsegs E m pib_vR.
Proof.
intros E m v kids keys n cap E19 X16 X17 X18 X19 Hv0 Hv1 Hw (_ & Hty & _ & _ & Hk & Hy & Hn & Hc).
unfold pib_vR, pib_vch.
apply (fsw_pj_part_okW tfibsegs _ _ 19 v v 0 56 0 56); [lia | lia | exact Hw | exact E19 | lia | lia | right; lia |].
constructor; [|constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]]].
- apply (fsw_pj_chunk4 tfibsegs _ _ v 0 (SLit 6) 6); [rewrite Z.add_0_r; exact Hty | reflexivity].
- apply (fsw_pj_chunk8 tfibsegs _ _ v 24 _ kids); [exact Hk | rewrite fsw_SOff0; exact X16].
- apply (fsw_pj_chunk8 tfibsegs _ _ v 32 _ keys); [exact Hy | rewrite fsw_SOff0; exact X17].
- apply (fsw_pj_chunk8 tfibsegs _ _ v 40 _ n); [exact Hn | rewrite fsw_SOff0; exact X18].
- apply (fsw_pj_chunk8 tfibsegs _ _ v 48 _ cap); [exact Hc | rewrite fsw_SOff0; exact X19].
Qed.

(* the resume regions are pairwise apart: the frame and q above alloc_ceiling, the two image cells, v off the image *)
Lemma pivm_disj : forall E sp q v, bv_unsigned (ew E 2) = sp - 144 -> bv_unsigned (ew E 9) = q ->
  bv_unsigned (ew E 19) = v -> alloc_ceiling <= sp - 144 -> sp <= q -> q + 24 <= 2 ^ 47 -> 4096 <= v ->
  v + 56 <= alloc_ceiling -> piv_hide (v + 56 <= 0x10000 \/ FS_IMG_END <= v) ->
  pairwise_disjoint E (fsT_ret_regions 144 pib_csL pib_rs).
Proof.
intros E sp q v E2 E9 E19 Hc Hq Hq1 Hv0 Hv1 Hvi. pose proof asan_consts as (C1 & _).
unfold fsT_ret_regions, fstk_ret, fs_got_region, fs_bcell_region, pib_rs, pi_qR, pib_vR.
cbn [app pairwise_disjoint all_disjoint]. unfold extent_disjoint.
cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E2, E9, E19.
unfold tfib_D_GOT_asan_shadow_memory_dynamic_address, tfib_D_asan_shadow_memory_dynamic_address, FS_IMG_END in *.
repeat match goal with |- _ /\ _ => split end; try exact I; piv_pd.
Qed.

(* the atom facts pib_gfP *)
Lemma pivm_gfP_ok : forall E q v p e d kids keys n cap a klen,
  bv_unsigned (ew E 9) = q -> bv_unsigned (ew E 19) = v ->
  ew E (xatom 0) = Z_to_bv 64 p -> ew E (xatom 1) = Z_to_bv 64 e -> ew E (xatom 2) = Z_to_bv 64 d ->
  ew E (xatom 16) = Z_to_bv 64 kids -> ew E (xatom 17) = Z_to_bv 64 keys ->
  ew E (xatom 18) = Z_to_bv 64 n -> ew E (xatom 19) = Z_to_bv 64 cap ->
  ew E (xatom 20) = Z_to_bv 64 a -> ew E (xatom 21) = Z_to_bv 64 klen ->
  2 ^ 46 <= q <= 2 ^ 47 - 24 -> q mod 8 = 0 -> 4096 <= v <= 2 ^ 47 - 56 -> v mod 8 = 0 ->
  4096 <= p <= 2 ^ 47 - 2 ^ 23 -> 4096 <= e <= 2 ^ 47 - 2 ^ 23 -> 1 <= d <= 2 ->
  4096 <= kids <= 2 ^ 47 - 2 ^ 23 -> kids mod 16 = 0 -> 4096 <= keys <= 2 ^ 47 - 2 ^ 23 -> keys mod 16 = 0 ->
  0 <= n <= 2 ^ 54 -> 0 <= cap <= 2 ^ 54 -> 4096 <= a <= 2 ^ 47 - 2 ^ 23 -> 0 <= klen <= 2 ^ 54 ->
  atoms_ok E pib_gfP.
Proof.
intros E q v p e d kids keys n cap a klen E9 E19 X0 X1 X2 X16 X17 X18 X19 X20 X21 Hq Hq8 Hv Hv8 Hp He Hd Hk Hk16
  Hy Hy16 Hn Hc Ha Hl.
unfold pib_gfP, pib_gf. cbn [app atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E9, E19, X0, X1, X2, X16, X17, X18, X19, X20, X21.
rewrite (wz p), (wz e), (wz d), (wz kids), (wz keys), (wz n), (wz cap), (wz a), (wz klen) by lia.
change (2 ^ 3) with 8. change (2 ^ 0) with 1. change (2 ^ 4) with 16.
repeat split; try lia; try apply Z.mod_1_r; assumption.
Qed.

(* the T resume after a runtime call at a raised window top ot (A walk's pic_resumeT, its chunks read on the memory
   after the call) *)
Lemma pivm_resumeT : forall B STK ot FP ly S W0 mem md own lyc Sc U2 (W : world tfibsegs) mem2 md2 kj regs2 sf f xs
  cs rs gf r,
  as_got_shadow B = tfib_D_GOT_asan_shadow_memory_dynamic_address ->
  as_shadow_cell B = tfib_D_asan_shadow_memory_dynamic_address ->
  @ajournal rc SK tfibsegs B STK ot FP ly S W0 mem md own lyc Sc W (unpoison U2 mem2) md2 kj ->
  ARU tfibsegs B lyc Sc U2 W mem2 md2 ->
  spZ regs2 = sf - f -> 0 < f -> (sf - f) mod 16 = 0 -> ot - STK <= sf - f -> sf <= ot ->
  regions_wf (fsT_ret_regions f cs rs) = true ->
  Forall (YP09.chunk_ok tfibsegs (Ereg regs2 (fs_extraT ++ xs)) (mrestrict (w_H W) mem2) (sf - f)) cs ->
  Forall (region_ok tfibsegs (Ereg regs2 (fs_extraT ++ xs)) (mrestrict (w_H W) mem2)) rs ->
  pairwise_disjoint (Ereg regs2 (fs_extraT ++ xs)) (fsT_ret_regions f cs rs) ->
  atoms_ok (Ereg regs2 (fs_extraT ++ xs)) gf ->
  st_ok tfibsegs (Ereg regs2 (fs_extraT ++ xs)) (fss_retT r f cs rs gf)
    (restrict (w_H W) (mkst regs2 (Z_to_bv 64 r) mem2 (seg_rom tfibsegs))).
Proof.
intros B STK ot FP ly S W0 mem md own lyc Sc U2 W mem2 md2 kj regs2 sf f xs cs rs gf r
  Hgot Hcell HJ HARU Usp Hf Hal Hlo Hsf Hwf Hcs Hrs Hpd Hgf.
pose proof asan_consts as (C1 & _ & C3 & _).
pose proof HJ as (HAR2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
assert (E2 : bv_unsigned (ew (Ereg regs2 (fs_extraT ++ xs)) 2) = sf - f)
  by (rewrite (ew_Ereg_nat regs2 (fs_extraT ++ xs) 2 2%bv eq_refl); exact Usp).
assert (E32 : ew (Ereg regs2 (fs_extraT ++ xs)) 32 = Z_to_bv 64 SHADOW_OFF)
  by (change 32%nat with (32 + 0)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (U32 : bv_unsigned (ew (Ereg regs2 (fs_extraT ++ xs)) 32) = SHADOW_OFF)
  by (rewrite E32; apply wz; unfold SHADOW_OFF; lia).
destruct (fsw_got_shadow B lyc Sc W (unpoison U2 mem2) md2 Hgot Hcell HAR2) as [Kgot Kcell].
assert (MB : forall x, 0 <= x < SHADOW_OFF ->
  mbyte tfibsegs (mrestrict (w_H W) mem2) x = mbyte tfibsegs (mrestrict (w_H W) (unpoison U2 mem2)) x).
{ intros x Hx. unfold mbyte, mrestrict.
  rewrite (ARU_mem_low tfibsegs B lyc Sc U2 W mem2 md2 (Z_to_bv 64 x) HARU
    ltac:(rewrite (wz x ltac:(unfold SHADOW_OFF in *; lia)); unfold SHADOW_OFF in *; lia)).
  reflexivity. }
assert (VM : forall a vv, 0 <= a -> a + 8 <= SHADOW_OFF ->
  val_mem tfibsegs (mrestrict (w_H W) (unpoison U2 mem2)) a 8 vv -> val_mem tfibsegs (mrestrict (w_H W) mem2) a 8 vv).
{ intros a vv Ha Hb Hv k0 Hk0. rewrite (MB (a + Z.of_nat k0) ltac:(lia)). exact (Hv k0 Hk0). }
assert (Vgot : val_mem tfibsegs (mrestrict (w_H W) mem2) tfib_D_GOT_asan_shadow_memory_dynamic_address 8
  tfib_D_asan_shadow_memory_dynamic_address).
{ apply VM; [unfold tfib_D_GOT_asan_shadow_memory_dynamic_address; lia
  | unfold tfib_D_GOT_asan_shadow_memory_dynamic_address, SHADOW_OFF; lia
  | exact (val_mem_of_rdword tfibsegs (w_H W) (unpoison U2 mem2) _ _ Kgot)]. }
assert (Vcell : val_mem tfibsegs (mrestrict (w_H W) mem2) tfib_D_asan_shadow_memory_dynamic_address 8 SHADOW_OFF).
{ apply VM; [unfold tfib_D_asan_shadow_memory_dynamic_address; lia
  | unfold tfib_D_asan_shadow_memory_dynamic_address, SHADOW_OFF; lia
  | exact (val_mem_of_rdword tfibsegs (w_H W) (unpoison U2 mem2) _ _ Kcell)]. }
rewrite restrict_mkst_fx. unfold fss_retT, fsT_ret_regions in *. cbn [app] in *. apply (entry_st_ok_full tfibsegs).
- apply regs_ok_Ereg.
- exact Hwf.
- constructor; [|constructor; [|constructor; [|exact Hrs]]].
  + unfold region_ok, fstk_ret. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E2. split; [lia|]. split; [lia|]. split.
    * intros o Ho. apply (apresent_writable tfibsegs).
      apply (fsw_apresent_unpoison B lyc Sc U2 W mem2 md2 _ HARU); [lia|]. apply Hpres. lia.
    * exact Hcs.
  + unfold fs_got_region, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    split; [unfold tfib_D_GOT_asan_shadow_memory_dynamic_address; lia|].
    split; [unfold tfib_D_GOT_asan_shadow_memory_dynamic_address; lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val tfibsegs _ _ 0 tfib_D_GOT_asan_shadow_memory_dynamic_address 8
      (SLit tfib_D_asan_shadow_memory_dynamic_address) tfib_D_asan_shadow_memory_dynamic_address);
      [reflexivity | unfold tfib_D_asan_shadow_memory_dynamic_address; cbn [Z.of_N]; lia | cbn [Z.of_N]; lia
      | cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]; rewrite Z.add_0_l; exact Vgot].
  + unfold fs_bcell_region, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    split; [unfold tfib_D_asan_shadow_memory_dynamic_address; lia|].
    split; [unfold tfib_D_asan_shadow_memory_dynamic_address; lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val tfibsegs _ _ 0 tfib_D_asan_shadow_memory_dynamic_address 8 (SOff 32 0) SHADOW_OFF);
      [rewrite fsw_SOff0, E32; reflexivity | unfold SHADOW_OFF; cbn [Z.of_N]; lia | cbn [Z.of_N]; lia
      | cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]; rewrite Z.add_0_l; exact Vcell].
- exact Hpd.
- split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok at 1 2. cbn [af_lo af_hi af_al2].
  rewrite E2, U32. split; [|split; [|exact Hgf]].
  + change (2 ^ 4) with 16. split; [lia|]. split; [exact Hal | lia].
  + rewrite Z.pow_0_r. split; [lia | split; [apply Z.mod_1_r | lia]].
Qed.

(* ---- segment G's start state, from the resume state by the kit (measured: every write window closed) ---- *)
Lemma pivm_ss_G_is : pib_ss_G = pik_addf (pik_setr (pik_setm (fss_retT 0x85170 144 pib_csL pib_rs pib_gfP)
  (pib_rgs pib_csL pib_RO pib_RO pib_RO)) pib_RL) pib_gf_vk [pib_c_m56; pib_geu (xatom 23) (xatom 16)] [pib_al_vk].
Proof. reflexivity. Qed.
Lemma pivm_rgs_sub : submem (pib_rgs pib_csL pib_RO pib_RO pib_RO)
  (ss_mem (fss_retT 0x85170 144 pib_csL pib_rs pib_gfP)).
Proof.
unfold pib_rgs, pib_RO, fss_retT, fsT_ret_regions, fstk_ret, pib_rs, pi_qR, pib_vR, fs_got_region, fs_bcell_region.
cbn [ss_mem app fst snd].
repeat (apply submem_keep; [unfold subregion; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks];
  split; [reflexivity|]; split; [lia|]; split; [lia|]; split; [left; lia | intros c Hc; exact Hc]|]).
apply submem_nil.
Qed.
Lemma pivm_rgs_wf : regions_wf (pib_rgs pib_csL pib_RO pib_RO pib_RO) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma pivm_ret_wf : regions_wf (fsT_ret_regions 144 pib_csL pib_rs) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma pivm_no_wr : forall E a, ~ in_wrange E (ss_mem pib_ss_G) a.
Proof.
intros E a (r & Hin & Hr).
assert (H : forallb (fun r => Z.eqb (YP09.r_wlo r) 0 && Z.eqb (YP09.r_whi r) 0) (ss_mem pib_ss_G) = true)
  by (vm_compute; reflexivity).
rewrite forallb_forall in H. pose proof (H r Hin) as Hb. apply andb_prop in Hb as [H1 H2].
apply Z.eqb_eq in H1. apply Z.eqb_eq in H2. rewrite H1, H2 in Hr. lia.
Qed.
(* segment G's stop (measured): parse_value, ra 0x851d0, a0 = q, a1 = the kid (xatom 23), the loop's registers *)
Definition pivm_stopR : list (bv 5 * sv) :=
  [(1%bv, SLit 0x851d0); (2%bv, SOff 2 0); (3%bv, SOff 3 0); (4%bv, SOff 4 0); (9%bv, SOff 9 0);
   (10%bv, SOff 9 0); (11%bv, SOff (xatom 23) 0); (19%bv, SOff 19 0)] ++ pib_RL.
Lemma pivm_fin_G : ss_pc (sh_ss pib_st_G) = A_parse_value /\ sh_obls pib_st_G = [] /\
  ss_resv (sh_ss pib_st_G) = None /\ sh_j pib_st_G = 0%nat /\ pib_regs_are (sh_ss pib_st_G) pivm_stopR = true.
Proof. vm_compute. repeat split; reflexivity. Qed.

(* ---- segment G's facts: the kid atom, the UBSan conditions, the kid's alias ---- *)
Lemma pivm_gf_vk : forall E dk, ew E (xatom 23) = Z_to_bv 64 dk -> 4096 <= dk <= 2 ^ 47 - 2 ^ 23 -> dk mod 8 = 0 ->
  atoms_ok E pib_gf_vk.
Proof.
intros E dk X Hd H8. unfold pib_gf_vk. cbn [atoms_ok]. split; [|exact I]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite X, wz by lia. change (2 ^ 3) with 8. lia.
Qed.
Lemma pivm_conds : forall E kids n, ew E (xatom 16) = Z_to_bv 64 kids -> ew E (xatom 18) = Z_to_bv 64 n ->
  ew E (xatom 23) = Z_to_bv 64 (kids + 56 * n) -> 0 <= kids -> 0 <= n <= 2 ^ 54 -> kids + 56 * n < 2 ^ 64 ->
  conds_ok E [pib_c_m56; pib_geu (xatom 23) (xatom 16)].
Proof.
intros E kids n X16 X18 X23 Hk Hn Hkn. cbn [conds_ok]. split; [|split; [|exact I]].
- unfold acond_ok, pib_c_m56. cbn [ac_c ac_a ac_b].
  assert (Un : YP0e.U E (SOff (xatom 18) 0) = n) by (apply U_atom; [exact X18 | lia]).
  assert (UM : YP0e.U E (SMd M_MUL (SOff (xatom 18) 0) (SLit 56)) = n * 56).
  { rewrite U_SMd. cbn [zmd_raw]. rewrite Un, U_lit by lia. apply zcanon_small. lia. }
  assert (UH : YP0e.U E (SMd M_MULH (SOff (xatom 18) 0) (SLit 56)) = 0).
  { rewrite U_SMd. cbn [zmd_raw]. rewrite Un, U_lit by lia.
    rewrite (swrap64_id n), (swrap64_id 56) by (unfold half64; lia).
    change (Z.of_N 64) with 64. rewrite Z.shiftr_div_pow2 by lia. rewrite (Z.div_small (n * 56)) by lia. reflexivity. }
  assert (US : YP0e.U E (SAlu ALU_SRA (SMd M_MUL (SOff (xatom 18) 0) (SLit 56)) (SLit 63)) = 0).
  { rewrite U_SAlu, UM, U_lit by lia. cbn [zalu_raw]. rewrite (swrap64_id (n * 56)) by (unfold half64; lia).
    change (Z.land 63 63) with 63. rewrite Z.shiftr_div_pow2 by lia. rewrite (Z.div_small (n * 56)) by lia. reflexivity. }
  rewrite branch_eq_U, U_SAlu. rewrite (U_SAlu E ALU_XOR), UH, US, !U_lit by lia. cbn [zalu_raw]. reflexivity.
- unfold acond_ok, pib_geu. cbn [ac_c ac_a ac_b].
  rewrite branch_geu_U. rewrite (U_atom E (xatom 23) _ X23) by lia. rewrite (U_atom E (xatom 16) _ X16) by lia.
  apply negb_true_iff, Z.ltb_ge. lia.
Qed.
Lemma pivm_al_vk : forall E kids n, ew E (xatom 16) = Z_to_bv 64 kids -> ew E (xatom 18) = Z_to_bv 64 n ->
  ew E (xatom 23) = Z_to_bv 64 (kids + 56 * n) -> 0 <= kids -> 0 <= n <= 2 ^ 54 -> kids + 56 * n < 2 ^ 64 ->
  alias_ok E [pib_al_vk].
Proof.
intros E kids n X16 X18 X23 Hk Hn Hkn. unfold pib_al_vk, pib_n56. cbn [alias_ok]. split; [|exact I].
apply pik_U_eq. rewrite !U_SAlu, !U_lit by lia.
rewrite (U_atom E (xatom 16) kids X16) by lia. rewrite (U_atom E (xatom 18) n X18) by lia.
rewrite (U_atom E (xatom 23) _ X23) by lia.
cbn [zalu_raw]. change (Z.land 6 63) with 6. change (Z.land 3 63) with 3.
rewrite !Z.shiftl_mul_pow2 by lia. change (2 ^ 6) with 64. change (2 ^ 3) with 8.
rewrite (zcanon_small (n * 64)), (zcanon_small (n * 8)) by lia. rewrite (zcanon_small (n * 64 - n * 8)) by lia.
rewrite zcanon_small by lia. lia.
Qed.

(* ---- the memory facts across the memset (copies of FSW_pj_set_rt.v pSr_hull_raw / pSr_present_raw, renamed) ---- *)
Lemma pivm_hull_raw : forall (W : world tfibsegs) U mem x n, upoisoned tfibsegs W mem U ->
  0 <= x -> x + n <= 2 ^ 63 -> 0 < n ->
  shadow_hull_vis (aview tfibsegs (w_H W) (unpoison U mem)) x n -> shadow_hull_vis (aview tfibsegs (w_H W) mem) x n.
Proof.
intros W U mem x n HP Hx Hxn Hn Hh s Hs.
assert (Rs : 0 <= s < 2 ^ 64) by (unfold shadow_addr, SHADOW_OFF in Hs; Z.div_mod_to_equations; lia).
destruct (in_ush U (bv_unsigned (Z_to_bv 64 s))) eqn:EU.
- rewrite (wz s Rs) in EU. rewrite (HP s EU). discriminate.
- rewrite <- (aview_unpoison_out tfibsegs (w_H W) U mem s EU). exact (Hh s Hs).
Qed.
Lemma pivm_present_raw : forall B ly S U (W : world tfibsegs) mem md a, ARU tfibsegs B ly S U W mem md ->
  0 <= a < 2 ^ 64 -> ~ (SHADOW_OFF <= a < SHADOW_OFF + 2 ^ 44) ->
  apresent (w_H W) (unpoison U mem) a -> apresent (w_H W) mem a.
Proof.
intros B ly S U W mem md a HARU Ha Hns (Hh & b & Hb). split; [exact Hh|]. exists b.
rewrite <- (fsw_unpoison_app B ly S U W mem md a HARU Ha Hns). exact Hb.
Qed.
(* the facts the intrinsic contract asks of 56 bytes of a live block's body, on the machine's memory *)
Lemma pivm_blk_facts : forall B ly S U (W : world tfibsegs) mem md P N d,
  ARU tfibsegs B ly S U W mem md -> FSupoisonU.fs_heads B ly S U -> In (P, N) (ablocks B ly S) ->
  P + HEAD <= d -> d + 56 <= P + req_size N ->
  4096 <= d /\ d + 56 <= alloc_ceiling /\ amem_range d 56 /\
  (forall x, d <= x < d + 56 -> apresent (w_H W) mem x /\ ~ aowned B ly S x) /\
  shadow_hull_vis (aview tfibsegs (w_H W) mem) d 56 /\
  range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF d 56.
Proof.
intros B ly S U W mem md P N d HARU HHD Hin H1 H2.
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof (proj1 HARU) as HAR. pose proof asan_consts as (C1 & _).
assert (HH : HEAD = 16) by reflexivity.
destruct (al_blocks _ _ LAWS ly S W (unpoison U mem) md P N HAR Hin) as (_ & H4096 & Hc & _ & Hb & _).
split; [lia|]. split; [lia|].
split; [exact (amem_range_of_block tfibsegs B LAWS ly S W (unpoison U mem) md P N d 56 HAR Hin ltac:(lia) H2)|].
split.
- intros x Hx. destruct (Hb x ltac:(lia)) as (Hp & Hno). split; [|exact Hno].
  apply (pivm_present_raw B ly S U W mem md x HARU); [lia | | exact Hp].
  exact (fsw_ablock_off_shadow B ly S W (unpoison U mem) md P N HAR Hin x ltac:(lia)).
- split.
  + apply (pivm_hull_raw W U mem d 56 (proj2 (proj2 HARU))); [lia | lia | lia |].
    exact (shadow_hull_vis_of_block tfibsegs B LAWS ly S W (unpoison U mem) md P N d 56 HAR Hin ltac:(lia) H2 ltac:(lia)).
  + exact (fsw_block_body_addressable B ly S U W mem md P N d 56 HARU HHD Hin ltac:(lia) ltac:(lia) H2).
Qed.
(* a live block's byte is writable on the machine's memory *)
Lemma pivm_blk_wr : forall B ly S U (W : world tfibsegs) mem md P N x,
  ARU tfibsegs B ly S U W mem md -> In (P, N) (ablocks B ly S) -> P <= x < P + req_size N ->
  writable_at tfibsegs (mrestrict (w_H W) mem) x.
Proof.
intros B ly S U W mem md P N x HARU Hin Hx. pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof (proj1 HARU) as HAR.
pose proof asan_consts as (C1 & _).
destruct (al_blocks _ _ LAWS ly S W (unpoison U mem) md P N HAR Hin) as (_ & H4096 & Hc & _ & Hb & _).
destruct (Hb x Hx) as (Hp & _). apply (apresent_writable tfibsegs).
apply (pivm_present_raw B ly S U W mem md x HARU); [lia | | exact Hp].
exact (fsw_ablock_off_shadow B ly S W (unpoison U mem) md P N HAR Hin x Hx).
Qed.
Lemma pivm_aview_some : forall (H : word -> bool) (m : word -> option byte) x z, aview tfibsegs H m x = Some z ->
  mbyte tfibsegs (mrestrict H m) x = Some (Z_to_bv 8 z).
Proof.
intros H m x z E. unfold aview in E. destruct (mbyte tfibsegs (mrestrict H m) x) as [b|]; cbn [option_map] in E;
  [|discriminate E].
injection E as <-. rewrite Z_to_bv_bv_unsigned. reflexivity.
Qed.
Lemma pivm_aview_unp : forall (H : word -> bool) U (m m' : word -> option byte) a,
  aview tfibsegs H m' a = aview tfibsegs H m a -> aview tfibsegs H (unpoison U m') a = aview tfibsegs H (unpoison U m) a.
Proof.
intros H U m m' a E. destruct (in_ush U (bv_unsigned (Z_to_bv 64 a))) eqn:EU.
- apply (aview_unpoison_in tfibsegs). exact EU.
- rewrite !(aview_unpoison_out tfibsegs) by exact EU. exact E.
Qed.
(* struct pj_in across a memory that agrees raw on q's 24 bytes and on the text *)
Lemma pivm_in_keep : forall m m' q text len p d tb, PjIn.pj_in_ok tfibsegs m q text len p d tb ->
  pim_eqon m m' q (q + 24) -> pim_eqon m m' text (text + len) -> PjIn.pj_in_ok tfibsegs m' q text len p d tb.
Proof.
intros m m' q text len p d tb (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12) Eq Et.
refine (conj _ (conj _ (conj _ (conj _ (conj H5 (conj H6 (conj H7 (conj H8 (conj H9 (conj _ (conj H11 H12))))))))))).
- apply (pim_eqon_bytes m m' q); [|exact H1]. rewrite Mem.length_le8. eapply pim_eqon_sub; [exact Eq | lia | lia].
- apply (pim_eqon_bytes m m' (q + 8)); [|exact H2]. rewrite Mem.length_le8. eapply pim_eqon_sub; [exact Eq | lia | lia].
- apply (pim_eqon_bytes m m' (q + 16)); [|exact H3]. rewrite Mem.length_le4. eapply pim_eqon_sub; [exact Eq | lia | lia].
- apply (pim_eqon_wr m m' q 24); [exact Eq | exact H4].
- apply (pim_eqon_bytes m m' text); [|exact H10]. rewrite H9. exact Et.
Qed.
(* the member loop's frame words across a memory that agrees on the frame's bytes *)
Lemma pivm_frameL_mb : forall (M M' : word -> option byte) sp xr q v,
  (forall a, sp - 144 <= a < sp -> mbyte tfibsegs M' a = mbyte tfibsegs M a) ->
  pib_frameL M sp xr q v -> pib_frameL M' sp xr q v.
Proof.
intros M M' sp xr q v E (H0 & H1 & H2 & H3 & H4 & H5).
assert (V : forall a x, sp - 144 <= a -> a + 8 <= sp -> val_mem tfibsegs M a 8 x -> val_mem tfibsegs M' a 8 x).
{ intros a x Ha Hn Hv. apply (pim_val_mb M M' a 8 x); [|exact Hv]. intros i Hi. apply E. change (Z.of_nat 8) with 8 in Hi. lia. }
split; [|split; [|split; [|split; [|split]]]].
- unfold pib_frame0 in *. rewrite Forall_forall in *. intros j Hj. pose proof (H0 j Hj) as Hv. apply in_seq in Hj.
  apply V; [lia | lia | exact Hv].
- apply V; [lia | lia | exact H1].
- apply V; [lia | lia | exact H2].
- apply V; [lia | lia | exact H3].
- apply V; [lia | lia | exact H4].
- apply V; [lia | lia | exact H5].
Qed.

End MH.

(* ================= image-free facts of the resume at 0x851d0 ================= *)
Section FV. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* the extra words of the resume env, by index *)
Lemma pivv_xsK_nth : forall p0 e0 d0 (xr0 : list word) kids keys n0 cap a klen, length xr0 = 13%nat ->
  let xs := pib_xsK p0 e0 d0 xr0 kids keys n0 cap a klen in
  nth 0 xs (Z_to_bv 64 0) = Z_to_bv 64 p0 /\ nth 1 xs (Z_to_bv 64 0) = Z_to_bv 64 e0 /\
  nth 2 xs (Z_to_bv 64 0) = Z_to_bv 64 d0 /\
  (forall j, (j < 13)%nat -> nth (3 + j) xs (Z_to_bv 64 0) = nth j xr0 (Z_to_bv 64 0)) /\
  nth 16 xs (Z_to_bv 64 0) = Z_to_bv 64 kids /\ nth 17 xs (Z_to_bv 64 0) = Z_to_bv 64 keys /\
  nth 18 xs (Z_to_bv 64 0) = Z_to_bv 64 n0 /\ nth 19 xs (Z_to_bv 64 0) = Z_to_bv 64 cap /\
  nth 20 xs (Z_to_bv 64 0) = Z_to_bv 64 a /\ nth 21 xs (Z_to_bv 64 0) = Z_to_bv 64 klen.
Proof.
intros p0 e0 d0 xr0 kids keys n0 cap a klen Hl xs. unfold xs, pib_xsK, pib_xs.
destruct xr0 as [|x0 [|x1 [|x2 [|x3 [|x4 [|x5 [|x6 [|x7 [|x8 [|x9 [|x10 [|x11 [|x12 [|x13 xrr]]]]]]]]]]]]]];
  try discriminate.
repeat split; try reflexivity.
intros j Hj. do 13 (destruct j as [|j]; [cbn [Nat.add app nth]; reflexivity|]). exfalso. revert Hj. cbn. lia.
Qed.
(* the member loop's frame across a memory change that keeps [sp - 144, sp) *)
Lemma pivv_frameL_mb : forall (M M' : word -> option byte) sp xr0 q0 v0,
  (forall a, sp - 144 <= a < sp -> mbyte tfibsegs M' a = mbyte tfibsegs M a) ->
  pib_frameL M sp xr0 q0 v0 -> pib_frameL M' sp xr0 q0 v0.
Proof.
intros M M' sp xr0 q0 v0 E (HF0 & F0 & F8 & F16 & F24 & F32).
assert (V : forall a vv, sp - 144 <= a -> a + 8 <= sp -> val_mem tfibsegs M a 8 vv ->
  val_mem tfibsegs M' a 8 vv).
{ intros a vv H1 H2 H. apply (pim_val_mb M M' a 8 vv); [|exact H]. intros i Hi. apply E. cbn in Hi. lia. }
split.
- unfold pib_frame0 in *. rewrite Forall_forall in *. intros j Hj. pose proof (in_seq 13 0 j) as Hs.
  apply Hs in Hj. apply (V (sp - 8 - 8 * Z.of_nat j)); [lia | lia | apply HF0; apply in_seq; lia].
- split; [apply V; [lia | lia | exact F0]|].
  split; [apply V; [lia | lia | exact F8]|].
  split; [apply V; [lia | lia | exact F16]|].
  split; apply V; [lia | lia | exact F24 | lia | lia | exact F32].
Qed.
(* the object v at atom 19 (image B's s3) *)
Lemma piv_vR_ok : forall E m v0 num str kids keys n0 cap,
  bv_unsigned (ew E 19) = v0 -> ew E (xatom 16) = Z_to_bv 64 kids -> ew E (xatom 17) = Z_to_bv 64 keys ->
  ew E (xatom 18) = Z_to_bv 64 n0 -> ew E (xatom 19) = Z_to_bv 64 cap ->
  0 <= v0 -> v0 + 56 <= 2 ^ 64 -> (forall i, 0 <= i < 56 -> writable_at tfibsegs m (v0 + i)) ->
  PjStruct.pj_hdr tfibsegs m v0 6 num str kids keys n0 cap -> region_ok tfibsegs E m pib_vR.
Proof.
intros E m v0 num str kids keys n0 cap E19 X16 X17 X18 X19 Hv0 Hv1 Hw (_ & Hty & _ & _ & Hk & Hy & Hn & Hc).
apply (fsw_pj_part_okW tfibsegs E m 19 v0 v0 0 56 0 56);
  [lia | lia | exact Hw | exact E19 | lia | lia | right; lia |].
unfold pib_vch.
constructor; [|constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]]].
- apply (fsw_pj_chunk4 tfibsegs E m v0 0 (SLit 6) 6); [rewrite Z.add_0_r; exact Hty | reflexivity].
- apply (fsw_pj_chunk8 tfibsegs E m v0 24 _ kids); [exact Hk | rewrite fsw_SOff0; exact X16].
- apply (fsw_pj_chunk8 tfibsegs E m v0 32 _ keys); [exact Hy | rewrite fsw_SOff0; exact X17].
- apply (fsw_pj_chunk8 tfibsegs E m v0 40 _ n0); [exact Hn | rewrite fsw_SOff0; exact X18].
- apply (fsw_pj_chunk8 tfibsegs E m v0 48 _ cap); [exact Hc | rewrite fsw_SOff0; exact X19].
Qed.
(* the regions of the resume are pairwise disjoint: the frame below struct pj_in, both above alloc_ceiling, the
   object below it and off the image *)
Lemma piv_disj : forall E sp q0 v0,
  bv_unsigned (ew E 2) = sp -> bv_unsigned (ew E 9) = q0 -> bv_unsigned (ew E 19) = v0 ->
  0x7fff7f800000 <= sp -> sp + 144 <= q0 -> q0 + 24 <= 2 ^ 47 -> 4096 <= v0 -> v0 + 56 <= sp ->
  piv_hide (v0 + 56 <= 0x10000 \/ FS_IMG_END <= v0) ->
  pairwise_disjoint E (fsT_ret_regions 144 pib_csL pib_rs).
Proof.
intros E sp q0 v0 E2 E9 E19 Hsp Hq Hq1 Hv0 Hv1 Iv.
apply pairwise_disjoint_of_extents.
unfold fsT_ret_regions, fstk_ret, fs_got_region, fs_bcell_region, pib_rs, pi_qR, pib_vR, extent_of_region.
cbn [app map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E2, E9, E19.
unfold tfib_D_GOT_asan_shadow_memory_dynamic_address, tfib_D_asan_shadow_memory_dynamic_address, FS_IMG_END in *.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
repeat match goal with |- _ /\ _ => split end; try exact I; piv_pd.
Qed.
(* the atom facts of the resume *)
Lemma piv_gfP_ok : forall E q0 v0 p0 e0 d0 kids keys n0 cap a klen,
  bv_unsigned (ew E 9) = q0 -> bv_unsigned (ew E 19) = v0 ->
  ew E (xatom 0) = Z_to_bv 64 p0 -> ew E (xatom 1) = Z_to_bv 64 e0 -> ew E (xatom 2) = Z_to_bv 64 d0 ->
  ew E (xatom 16) = Z_to_bv 64 kids -> ew E (xatom 17) = Z_to_bv 64 keys ->
  ew E (xatom 18) = Z_to_bv 64 n0 -> ew E (xatom 19) = Z_to_bv 64 cap ->
  ew E (xatom 20) = Z_to_bv 64 a -> ew E (xatom 21) = Z_to_bv 64 klen ->
  2 ^ 46 <= q0 <= 2 ^ 47 - 24 -> q0 mod 8 = 0 -> 4096 <= v0 <= 2 ^ 47 - 56 -> v0 mod 8 = 0 ->
  4096 <= p0 <= 2 ^ 47 - 2 ^ 23 -> 4096 <= e0 <= 2 ^ 47 - 2 ^ 23 -> 1 <= d0 <= 2 ->
  4096 <= kids <= 2 ^ 47 - 2 ^ 23 -> kids mod 16 = 0 -> 4096 <= keys <= 2 ^ 47 - 2 ^ 23 -> keys mod 16 = 0 ->
  0 <= n0 <= 2 ^ 54 -> 0 <= cap <= 2 ^ 54 -> 4096 <= a <= 2 ^ 47 - 2 ^ 23 -> 0 <= klen <= 2 ^ 54 ->
  atoms_ok E pib_gfP.
Proof.
intros E q0 v0 p0 e0 d0 kids keys n0 cap a klen E9 E19 X0 X1 X2 X16 X17 X18 X19 X20 X21
  Hq Hq8 Hv Hv8 Hp He Hd Hk Hk16 Hy Hy16 Hn Hc Ha Hl.
unfold pib_gfP, pib_gf. cbn [app atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E9, E19, X0, X1, X2, X16, X17, X18, X19, X20, X21.
rewrite (wz p0), (wz e0), (wz d0), (wz kids), (wz keys), (wz n0), (wz cap), (wz a), (wz klen) by lia.
change (2 ^ 3) with 8. change (2 ^ 0) with 1. change (2 ^ 4) with 16.
repeat split; try lia; try apply Z.mod_1_r; assumption.
Qed.
Lemma piv_wf : regions_wf (fsT_ret_regions 144 pib_csL pib_rs) = true.
Proof. vm_compute. reflexivity. Qed.
End FV.

Section H. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma piv_swrap_small : forall z, 0 <= z < 2 ^ 63 -> bv_swrap 64 z = z.
Proof.
intros z Hz. apply bv_swrap_small. unfold bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 64 / 2) with (2 ^ 63).
lia.
Qed.
Lemma piv_c_n60_ok : forall E n, ew E (xatom 18) = Z_to_bv 64 n -> 0 <= n < 2 ^ 54 -> acond_ok E pib_c_n60.
Proof.
intros E n Hn Hr. unfold acond_ok, pib_c_n60. cbn [ac_c ac_a ac_b]. rewrite branch_eq_U.
rewrite U_SAlu, U_SLit, (U_atom_off E (xatom 18) n 1152921504606846976 Hn) by lia. cbn [zalu_raw].
replace (Z.land (zcanon 61) 63) with 61 by reflexivity. rewrite Z.shiftr_div_pow2 by lia.
rewrite (Z.div_small (n + 1152921504606846976) (2 ^ 61)) by lia. reflexivity.
Qed.
Lemma piv_c_m56_ok : forall E n, ew E (xatom 18) = Z_to_bv 64 n -> 0 <= n < 2 ^ 54 -> acond_ok E pib_c_m56.
Proof.
intros E n Hn Hr. unfold acond_ok, pib_c_m56. cbn [ac_c ac_a ac_b]. rewrite branch_eq_U.
rewrite !U_SAlu, !U_SMd, !U_SLit, (U_atom_off E (xatom 18) n 0 Hn) by lia. rewrite Z.add_0_r.
cbn [zalu_raw zmd_raw]. replace (zcanon 56) with 56 by reflexivity. replace (zcanon 63) with 63 by reflexivity.
replace (zcanon 0) with 0 by reflexivity. replace (Z.land 63 63) with 63 by reflexivity.
rewrite (piv_swrap_small n) by lia. rewrite (piv_swrap_small 56) by lia.
rewrite (zcanon_small (n * 56)) by lia. rewrite (piv_swrap_small (n * 56)) by lia.
change (Z.of_N 64) with 64. rewrite !Z.shiftr_div_pow2 by lia.
rewrite (Z.div_small (n * 56) (2 ^ 64)) by lia. rewrite (Z.div_small (n * 56) (2 ^ 63)) by lia. reflexivity.
Qed.
Lemma piv_geu_ok : forall E a b x y, ew E a = Z_to_bv 64 x -> ew E b = Z_to_bv 64 y -> 0 <= x < 2 ^ 64 ->
  0 <= y < 2 ^ 64 -> y <= x -> acond_ok E (pib_geu a b).
Proof.
intros E a b x y Ha Hb Hx Hy Hle. unfold acond_ok, pib_geu. cbn [ac_c ac_a ac_b]. rewrite branch_geu_U.
rewrite (U_atom E a x Ha Hx), (U_atom E b y Hb Hy). apply Bool.negb_true_iff. apply Z.ltb_ge. exact Hle.
Qed.
Lemma piv_al_vk_ok : forall E kids n, ew E (xatom 16) = Z_to_bv 64 kids -> ew E (xatom 18) = Z_to_bv 64 n ->
  0 <= kids -> 0 <= n < 2 ^ 54 -> kids + 56 * n < 2 ^ 64 -> ew E (xatom 23) = Z_to_bv 64 (kids + 56 * n) ->
  alias_ok E [pib_al_vk].
Proof.
intros E kids n Hk Hn Hk0 Hn0 Hkn Ht. cbn [alias_ok]. split; [|exact I]. apply pik_U_eq.
unfold pib_al_vk, pib_n56. cbn [fst snd].
rewrite !U_SAlu, !U_SLit. rewrite (U_atom_off E (xatom 18) n 0 Hn) by lia.
rewrite (U_atom_off E (xatom 16) kids 0 Hk) by lia. rewrite (U_atom_off E (xatom 23) (kids + 56 * n) 0 Ht) by lia.
rewrite !Z.add_0_r. cbn [zalu_raw]. replace (Z.land (zcanon 6) 63) with 6 by reflexivity.
replace (Z.land (zcanon 3) 63) with 3 by reflexivity. rewrite !Z.shiftl_mul_pow2 by lia.
change (2 ^ 6) with 64. change (2 ^ 3) with 8.
rewrite (zcanon_small (n * 64)) by lia. rewrite (zcanon_small (n * 8)) by lia.
rewrite (zcanon_small (n * 64 - n * 8)) by lia. rewrite zcanon_small by lia. lia.
Qed.
Lemma piv_wsc0_ok : forall E c0 e, ew E (xatom 0) = Z_to_bv 64 c0 -> ew E (xatom 1) = Z_to_bv 64 e ->
  0 <= c0 -> c0 < e -> e < 2 ^ 64 -> conds_ok E pib_wsc0.
Proof.
intros E c0 e H0 H1 Hc He He'. unfold pib_wsc0. cbn [conds_ok]. split; [|exact I].
apply (pik_cond_ltu E _ _ _ _ c0 e H0 H1); lia.
Qed.
End H.

(* ================= the resume env's atoms (pib_xsK) ================= *)
Section X. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma piv_xsK_nth : forall p e d xr kids keys n cap a klen, length xr = 13%nat ->
  nth 0 (pib_xsK p e d xr kids keys n cap a klen) (Z_to_bv 64 0) = Z_to_bv 64 p /\ nth 1 (pib_xsK p e d xr kids keys n cap a klen) (Z_to_bv 64 0) = Z_to_bv 64 e /\
  nth 2 (pib_xsK p e d xr kids keys n cap a klen) (Z_to_bv 64 0) = Z_to_bv 64 d /\
  (forall j, (j < 13)%nat -> nth (3 + j) (pib_xsK p e d xr kids keys n cap a klen) (Z_to_bv 64 0) = nth j xr (Z_to_bv 64 0)) /\
  nth 16 (pib_xsK p e d xr kids keys n cap a klen) (Z_to_bv 64 0) = Z_to_bv 64 kids /\ nth 17 (pib_xsK p e d xr kids keys n cap a klen) (Z_to_bv 64 0) = Z_to_bv 64 keys /\
  nth 18 (pib_xsK p e d xr kids keys n cap a klen) (Z_to_bv 64 0) = Z_to_bv 64 n /\ nth 19 (pib_xsK p e d xr kids keys n cap a klen) (Z_to_bv 64 0) = Z_to_bv 64 cap /\
  nth 20 (pib_xsK p e d xr kids keys n cap a klen) (Z_to_bv 64 0) = Z_to_bv 64 a /\ nth 21 (pib_xsK p e d xr kids keys n cap a klen) (Z_to_bv 64 0) = Z_to_bv 64 klen /\
  nth 22 (pib_xsK p e d xr kids keys n cap a klen) (Z_to_bv 64 0) = Z_to_bv 64 (keys + 8 * n) /\ nth 23 (pib_xsK p e d xr kids keys n cap a klen) (Z_to_bv 64 0) = Z_to_bv 64 (kids + 56 * n) /\
  length (pib_xsK p e d xr kids keys n cap a klen) = 24%nat.
Proof.
intros p e d xr kids keys n cap a klen Hl. set (xs := pib_xsK p e d xr kids keys n cap a klen). fold xs.
assert (Hp : length (pib_xs p e d xr kids keys n cap) = 20%nat)
  by (unfold pib_xs; rewrite !length_app, Hl; reflexivity).
assert (A1 : forall i, (i < 20)%nat -> nth i xs (Z_to_bv 64 0) = nth i (pib_xs p e d xr kids keys n cap) (Z_to_bv 64 0))
  by (intros i Hi; unfold xs, pib_xsK; apply app_nth1; lia).
assert (A2 : forall i, (20 <= i)%nat ->
  nth i xs (Z_to_bv 64 0) = nth (i - 20) [Z_to_bv 64 a; Z_to_bv 64 klen; Z_to_bv 64 (keys + 8 * n);
    Z_to_bv 64 (kids + 56 * n)] (Z_to_bv 64 0)).
{ intros i Hi. unfold xs, pib_xsK. rewrite app_nth2 by lia. rewrite Hp. reflexivity. }
assert (B1 : forall i, (3 <= i)%nat -> nth i (pib_xs p e d xr kids keys n cap) (Z_to_bv 64 0) =
  nth (i - 3) (xr ++ [Z_to_bv 64 kids; Z_to_bv 64 keys; Z_to_bv 64 n; Z_to_bv 64 cap]) (Z_to_bv 64 0)).
{ intros i Hi. unfold pib_xs. rewrite app_nth2 by (cbn [length]; lia). cbn [length]. reflexivity. }
repeat apply conj.
- rewrite (A1 0%nat ltac:(lia)). reflexivity.
- rewrite (A1 1%nat ltac:(lia)). reflexivity.
- rewrite (A1 2%nat ltac:(lia)). reflexivity.
- intros j Hj. rewrite (A1 (3 + j)%nat ltac:(lia)), (B1 (3 + j)%nat ltac:(lia)).
  replace (3 + j - 3)%nat with j by lia. apply app_nth1. lia.
- rewrite (A1 16%nat ltac:(lia)), (B1 16%nat ltac:(lia)), app_nth2 by lia. rewrite Hl. reflexivity.
- rewrite (A1 17%nat ltac:(lia)), (B1 17%nat ltac:(lia)), app_nth2 by lia. rewrite Hl. reflexivity.
- rewrite (A1 18%nat ltac:(lia)), (B1 18%nat ltac:(lia)), app_nth2 by lia. rewrite Hl. reflexivity.
- rewrite (A1 19%nat ltac:(lia)), (B1 19%nat ltac:(lia)), app_nth2 by lia. rewrite Hl. reflexivity.
- rewrite (A2 20%nat ltac:(lia)). reflexivity.
- rewrite (A2 21%nat ltac:(lia)). reflexivity.
- rewrite (A2 22%nat ltac:(lia)). reflexivity.
- rewrite (A2 23%nat ltac:(lia)). reflexivity.
- unfold xs, pib_xsK. rewrite length_app, Hp. reflexivity.
Qed.
End X.

(* ================= the measured segments E and F: their stops ================= *)
Section M2. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition piv_regs_E : list (bv 5 * sv) :=
  [(1%bv, SLit 0x850bc); (2%bv, SOff 2 0); (3%bv, SOff 3 0); (4%bv, SOff 4 0); (8%bv, SOff 9 16);
   (9%bv, SOff 9 0); (10%bv, SOff 9 0); (19%bv, SOff 19 0)] ++ pib_RL.
Lemma piv_fin_E :
  let s := sh_ss pib_st_E in
  ss_pc s = A_skip_ws /\ sh_obls pib_st_E = [] /\ ss_resv s = None /\ sh_j pib_st_E = 0%nat /\
  pib_regs_are s piv_regs_E = true /\
  nth_error (ss_mem s) 0 = Some (YP09.mkRegion (Some (xatom 22)) 0 8 0 8
    [YP09.mkChunk 0 (CVal 8 (SOff (xatom 20) 0))]) /\
  nth_error (ss_mem s) 1 = Some (YP09.mkRegion (Some 2%nat) 0 144 0 0 pib_csL) /\
  nth_error (ss_mem s) 4 = Some (YP09.mkRegion (Some 9%nat) 0 24 0 0 (YP09.r_chunks pi_qR)) /\
  run_K 0 fs_Bx pib_SHe pib_ss_E = 56%nat.
Proof. vm_compute. repeat split; reflexivity. Qed.
Definition piv_regs_F : list (bv 5 * sv) :=
  [(1%bv, SLit 0x85170); (2%bv, SOff 2 0); (3%bv, SOff 3 0); (4%bv, SOff 4 0); (8%bv, SOff 9 16);
   (9%bv, SOff 9 0); (10%bv, SOff (xatom 23) 0); (12%bv, SLit 56); (19%bv, SOff 19 0)] ++ pib_RL.
Lemma piv_fin_F :
  let s := sh_ss pib_st_F in
  ss_pc s = PC_memset /\ sh_obls pib_st_F = [] /\ ss_resv s = None /\ sh_j pib_st_F = 2%nat /\
  pib_regs_are s piv_regs_F = true /\
  sr_get (ss_regs s) 11%bv = SAlu ALU_SLTU (SLit 0) (SAlu ALU_XOR (SMd M_MULH (SOff (xatom 18) 0) (SLit 56))
    (SAlu ALU_SRA (SMd M_MUL (SOff (xatom 18) 0) (SLit 56)) (SLit 63))) /\
  nth_error (ss_mem s) 4 = Some (YP09.mkRegion (Some 9%nat) 0 24 0 24
    [YP09.mkChunk 0 (CVal 8 (SOff (xatom 0) 1)); YP09.mkChunk 8 (CVal 8 (SOff (xatom 1) 0));
     YP09.mkChunk 16 (CVal 4 (SOff (xatom 2) 0))]) /\
  nth_error (ss_mem s) 1 = Some (YP09.mkRegion (Some 2%nat) 0 144 0 0 pib_csL) /\
  run_K 0 fs_Bx pib_SHc pib_ss_F = 57%nat.
Proof. vm_compute. repeat split; reflexivity. Qed.
(* the write windows of the two start states: E writes the key slot only, F writes struct pj_in only *)
Lemma piv_wr_E : forall E x, in_wrange E (ss_mem pib_ss_E) x ->
  bv_unsigned (ew E (xatom 22)) <= x < bv_unsigned (ew E (xatom 22)) + 8.
Proof.
intros E x (r & Hin & Hr).
assert (Hm : ss_mem pib_ss_E = [pib_kaR; YP09.mkRegion (Some 2%nat) 0 144 0 0 pib_csL; fs_got_region;
  fs_bcell_region 32; YP09.mkRegion (Some 9%nat) 0 24 0 0 (YP09.r_chunks pi_qR);
  YP09.mkRegion (Some 19%nat) 0 56 0 0 pib_vch]) by reflexivity.
rewrite Hm in Hin. cbn [In] in Hin.
destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]];
  cbn [pib_kaR fs_got_region fs_bcell_region YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; lia.
Qed.
Lemma piv_wr_F : forall E x, in_wrange E (ss_mem pib_ss_F) x ->
  bv_unsigned (ew E 9) <= x < bv_unsigned (ew E 9) + 24.
Proof.
intros E x (r & Hin & Hr).
assert (Hm : ss_mem pib_ss_F = [pik_treg (xatom 0) 0 [58]; YP09.mkRegion (Some 2%nat) 0 144 0 0 pib_csL;
  fs_got_region; fs_bcell_region 32; YP09.mkRegion (Some 9%nat) 0 24 0 24 (YP09.r_chunks pi_qR);
  YP09.mkRegion (Some 19%nat) 0 56 0 0 pib_vch]) by reflexivity.
rewrite Hm in Hin. cbn [In] in Hin.
destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]];
  cbn [pik_treg fs_got_region fs_bcell_region YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; lia.
Qed.
(* the start states' region lists, narrowed from the resume's *)
Lemma piv_subreg_refl : forall r, subregion r r.
Proof.
intros r. unfold subregion. split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [|tauto].
destruct (Z.le_gt_cases (YP09.r_whi r) (YP09.r_wlo r)); [left; lia | right; lia].
Qed.
Lemma piv_submem_E : submem (pib_rgs pib_csL pib_RO pib_RO pib_RO) (fsT_ret_regions 144 pib_csL pib_rs).
Proof.
unfold fsT_ret_regions, pib_rgs, pib_rs, pib_RO, pi_qR, pib_vR. cbn [app fst snd].
apply submem_keep; [unfold subregion; cbn; repeat split; try lia; try (left; lia); tauto|].
apply submem_keep; [apply piv_subreg_refl|]. apply submem_keep; [apply piv_subreg_refl|].
apply submem_keep; [unfold subregion; cbn; repeat split; try lia; try (left; lia); tauto|].
apply submem_keep; [|apply submem_nil].
unfold subregion; cbn; repeat split; try lia; try (left; lia); tauto.
Qed.
Lemma piv_submem_F : submem (pib_rgs pib_csL pib_RO (0, 24) pib_RO) (fsT_ret_regions 144 pib_csL pib_rs).
Proof.
unfold fsT_ret_regions, pib_rgs, pib_rs, pib_RO, pi_qR, pib_vR. cbn [app fst snd].
apply submem_keep; [unfold subregion; cbn; repeat split; try lia; try (left; lia); tauto|].
apply submem_keep; [apply piv_subreg_refl|]. apply submem_keep; [apply piv_subreg_refl|].
apply submem_keep; [unfold subregion; cbn; repeat split; try lia; try (right; lia); tauto|].
apply submem_keep; [|apply submem_nil].
unfold subregion; cbn; repeat split; try lia; try (left; lia); tauto.
Qed.
Lemma piv_wf_E : regions_wf (pib_rgs pib_csL pib_RO pib_RO pib_RO) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma piv_wf_F : regions_wf (pib_rgs pib_csL pib_RO (0, 24) pib_RO) = true.
Proof. vm_compute. reflexivity. Qed.
End M2.

(* ================= the composition: parse_items_spec k's entry and the three callees ================= *)
Section PI. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Variables (k : nat) (ly : alayout) (S : astate) (U : list (Z * Z)) (W : world tfibsegs) (regs : bvmap 5 word)
  (mem : word -> option byte) (md : Model) (q ot v text len p tcap : Z) (tb : list byte)
  (ms : list (list Z * PjTree.jv)) (pr : bool) (rest : list Z) (live peak cnt fail : Z).
Let sp0 : Z := spZ regs.
Let dd : Z := Z.of_nat k.
Let FP : list (Z * Z) := [(v, v + 56)] ++ FS_PSTAT_FP.
Let STKt : Z := STK_parse_items (1 - k) + (ot - sp0).
Let xr : list word := map (YK11.getr regs) pi_saved_regs.
Variable ch : list (Z * Z * Z).
Hypothesis Hk : (k <= 1)%nat.
Hypothesis HSS : FsShadowSyms B.
Hypothesis HPRE : fpreU tfibsegs B (STK_parse_items (1 - k)) ly S U W regs mem md ch.
Hypothesis HHEADS : FSupoisonU.fs_heads B ly S U.
Hypothesis HWIN : rd_win tfibsegs regs ly W mem q ot.
Hypothesis HQ16 : spZ regs + 16 <= q.
Hypothesis HTX : rd_text tfibsegs B ly S W mem text len tcap.
Hypothesis HIN0 : PjIn.pj_in_ok tfibsegs (rdW W mem) q text len p dd tb.
Hypothesis HVTX : v + 56 <= text - HEAD \/ text + tcap <= v.
Hypothesis HPO0 : pobj tfibsegs B ly S W mem v.
Hypothesis HQT : quiet cnt fail (Z.of_nat (length (PjRoundTrip.ttrace (PjTree.JObj ms)))).
Hypothesis HSZ : rd_sizes_ok (PjRoundTrip.ttrace (PjTree.JObj ms)).
Hypothesis HLIVE : live + rd_live (PjRoundTrip.ttrace (PjTree.JObj ms)) < 2 ^ 64.
Hypothesis HEV : st_nev S + rd_ev (PjRoundTrip.ttrace (PjTree.JObj ms)) <= EV_MAX.
Hypothesis HBB : blocks_bytes S + rd_live (PjRoundTrip.ttrace (PjTree.JObj ms)) <= LIVE_MAX.
Hypothesis HFRL : Z.of_nat (length (frames S)) <= FRL_parse_value (Z.of_nat k + 1).
Hypothesis H10 : YK11.getr regs 10 = w64 q.
Hypothesis H11 : YK11.getr regs 11 = w64 v.
Hypothesis H12 : YK11.getr regs 12 = w64 1.
Hypothesis HCH0 : exists chq, achain ly (aview tfibsegs (w_H W) (unpoison U mem)) (spZ regs) q chq /\
  Forall (fun r => bad_next (fst (fst r)) (ly_top ly) (snd r) = true \/ q + 40 <= snd r) chq.
Hypothesis HREST : ReaderRes.rest_at tb text p = concat (WriterValue.wvpieces (PjTree.JObj ms) pr (Z.of_nat k)) ++ rest.
Hypothesis HDV : FSDocStrs.fs_doc_values (PjTree.JObj ms).
Hypothesis HDS : FSDocStrs.fs_doc_strings (PjTree.JObj ms).
Hypothesis HWF : PjRoundTrip.pj_wf ReaderRes.jr_strtod (PjTree.JObj ms).
Hypothesis HDEP : (PjTree.depth (PjTree.JObj ms) <= 2 - k)%nat.
Hypothesis HZERO : PjStruct.pj_zero tfibsegs (rdW W mem) v.
Hypothesis HVSP : v + 56 <= spZ regs - STK_parse_items (1 - k) \/ ot <= v.
Hypothesis HGLOB : fs_glob tfibsegs W mem live peak cnt fail.
(* the callees: skip_ws (a Theorem Labs lane's B walk), parse_value at level k + 1, and the runtime's __asan_memset (FsRt's
   field fr_memset, lib/B/FSH_Rt.v, at this build's PC_memset 0x5222c) *)
Hypothesis HSW : @skip_ws_spec fx rc SK tfibsegs B.
Hypothesis HPV : @parse_value_spec fx rc SK tfibsegs B (Datatypes.S k).
Hypothesis HMS : FSupoisonU.aintrin_realizesU tfibsegs B OSet PC_memset.
#[local] Abbreviation IE := (@pib_IE fx rc SK B k ly S U W regs mem md q ot v text len tcap tb ms pr rest live peak cnt fail).
#[local] Abbreviation IK := (@pib_IK rc SK B k ly S U W regs mem md q ot v text len tcap tb ms pr rest live peak cnt fail).
#[local] Abbreviation IM := (@pib_IM rc SK B k ly S U W regs mem md q ot v text len tcap tb ms pr rest live peak cnt fail).
#[local] Abbreviation IV := (@pib_IV rc SK B k ly S U W regs mem md q ot v text len tcap tb ms pr rest live peak cnt fail).
#[local] Abbreviation IH := (@pib_IH fx rc SK B k ly S U W regs mem md q ot v text len tcap tb ms pr rest live peak cnt fail).

(* ================= the call of __asan_memset (dk, 0, 56) at 0x85160 .. ra 0x85170 =================
   dk is 56 bytes of a live block (P, N) of the caller's state that is not the entry's (a temporary block: the kids
   array). The runtime contract fr_memset, the caller's journal put back on the memory after the call
   (FSW_K.fsw_intrin_atU); the continuation gets the journal, ARU, the preserved registers, a0, the zeroed bytes and
   the frame (the view kept off dk and off the call's stack window). *)
Lemma piv_call_ms : forall lyc Sc Uc (W1 : world tfibsegs) memC mdC kc regsC dk P N (Qc : world tfibsegs -> config -> Prop),
  @pib_jc rc SK B k ly S U W regs mem md ot v lyc Sc Uc W1 memC mdC kc ->
  pib_regsP B regs q v regsC pib_RL ->
  YK11.getr regsC 1 = w64 0x85170 -> YK11.getr regsC 10 = w64 dk -> YK11.getr regsC 11 = w64 0 ->
  YK11.getr regsC 12 = w64 56 ->
  In (P, N) (ablocks B lyc Sc) -> ~ In (P, N) (ablocks B ly S) -> P + HEAD <= dk -> dk + 56 <= P + req_size N ->
  (forall regs2 mem2 md2,
     @ajournal rc SK tfibsegs B (STK_parse_items (1 - k) + (ot - spZ regs)) ot ([(v, v + 56)] ++ FS_PSTAT_FP) ly S W
       (unpoison U mem) md [] lyc Sc W1 (unpoison Uc mem2) md2 kc ->
     ARU tfibsegs B lyc Sc Uc W1 mem2 md2 -> aregs_preserved regsC regs2 -> YK11.getr regs2 10 = w64 dk ->
     (forall i, 0 <= i < 56 -> aview tfibsegs (w_H W1) mem2 (dk + i) = Some 0) ->
     (forall a, 0 <= a < 2 ^ 64 -> ~ (dk <= a < dk + 56) -> ~ (spZ regs - 144 - ESTACK <= a < spZ regs - 144) ->
        aview tfibsegs (w_H W1) mem2 a = aview tfibsegs (w_H W1) memC a) ->
     SRr tfibsegs W1 (mkCfg (mkst regs2 (Z_to_bv 64 0x85170) mem2 (seg_rom tfibsegs)) md2) Qc) ->
  SRr tfibsegs W1 (YG0d.cfg_at tfibsegs PC_memset regsC memC mdC) Qc.
Proof.
intros lyc Sc Uc W1 memC mdC kc regsC dk P N Qc HJC HRP R1 R10 R11 R12 Hin Hnin Hd1 Hd2 K.
destruct HJC as (HJ & HARU & _ & HHD).
destruct HRP as (Rsp & _ & _ & R3 & R4 & _).
pose proof asan_consts as (C1 & _).
pose proof (piv_sp0 B k ly S U W regs mem md ot ms ch Hk HPRE HDEP) as (Hsp16 & Hsp1 & Hsp2).
pose proof HWIN as (Hsq & Hq24 & Hot16 & _).
assert (HSTK2 : ESTACK + 144 <= STK_parse_items (1 - k))
  by (unfold STK_parse_items, STK_parse_items_of, zmaxl, FRAME_parse_items, STK_RT_INTRIN; cbn [fold_right]; lia).
assert (EST : ESTACK = 4096) by reflexivity.
assert (HH : HEAD = 16) by reflexivity.
destruct (pivm_blk_facts B lyc Sc Uc W1 memC mdC P N dk HARU HHD Hin Hd1 Hd2) as (D1 & D2 & DAM & DPR & DHULL & DRA).
assert (HPREc : ecall_preU tfibsegs B lyc Sc Uc W1 regsC memC mdC).
{ refine (fsw_ecall_preU_at B (STK_parse_items (1 - k) + (ot - spZ regs)) ot ([(v, v + 56)] ++ FS_PSTAT_FP) ly S W
    (unpoison U mem) md [] lyc Sc Uc W1 memC mdC kc regsC (spZ regs - 144 - ot) HJ HARU _ _ _ _ _ R3 R4).
  - rewrite Rsp. lia.
  - clear - Hsp16 Hot16. Z.div_mod_to_equations. lia.
  - lia.
  - lia.
  - rewrite R1. apply ret_ok_even. vm_compute. reflexivity. }
assert (HDEST : dest_ok tfibsegs B lyc Sc W1 regsC memC dk 56).
{ intros a Ha. destruct (DPR a Ha) as (Hpa & Hno).
  split; [exact (apresent_writable tfibsegs _ _ _ Hpa)|]. split; [exact Hno|]. rewrite Rsp. lia. }
assert (ERA : raZ regsC = 0x85170) by (unfold raZ; rewrite R1; vm_compute; reflexivity).
eapply SRr_bind.
{ apply (fsw_intrin_atU B (STK_parse_items (1 - k) + (ot - spZ regs)) ot ([(v, v + 56)] ++ FS_PSTAT_FP) ly S W
    (unpoison U mem) md [] lyc Sc Uc W1 memC mdC kc Uc
    (fun a => dk <= a < dk + 56 \/ spZ regsC - ESTACK <= a < spZ regsC) (w64 (raZ regsC)) _
    (fun regs' mem' md' => aregs_preserved regsC regs' /\ YK11.getr regs' 10 = w64 dk /\
       (forall i, 0 <= i < 56 -> aview tfibsegs (w_H W1) mem' (dk + i) = Some 0) /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (dk <= a < dk + 56) -> ~ (spZ regsC - ESTACK <= a < spZ regsC) ->
          aview tfibsegs (w_H W1) mem' a = aview tfibsegs (w_H W1) memC a)) HJ).
  - eapply SRr_mono.
    { exact (HMS lyc Sc Uc W1 regsC memC mdC dk 0 56 HPREc R10 R11 R12 ltac:(lia) ltac:(lia)
        ltac:(lia) HDEST DAM DRA (fun _ => DHULL) I). }
    cbv beta. intros W' c' _ (-> & regs' & mem' & md' & -> & HARU' & HP' & Hsame & H10' & Hset & Hfr' & Hpr).
    split; [reflexivity|]. exists regs', mem', md'.
    split; [reflexivity|]. split; [exact HARU'|]. split; [exact Hsame|].
    split.
    { intros a Ha HnW.
      destruct (in_ush Uc (bv_unsigned (Z_to_bv 64 a))) eqn:EU.
      - apply (aview_unpoison_in tfibsegs). exact EU.
      - rewrite !(aview_unpoison_out tfibsegs) by exact EU.
        apply Hfr'; [exact Ha | intros Hx; apply HnW; left; exact Hx | intros Hx; apply HnW; right; exact Hx]. }
    split.
    { intros a (Hh & b & Hb). split; [exact Hh|].
      destruct (in_ush Uc (bv_unsigned (Z_to_bv 64 a))) eqn:EU.
      - exists (Z_to_bv 8 0). apply unpoison_in. exact EU.
      - rewrite (unpoison_out Uc mem' (Z_to_bv 64 a) EU). rewrite (unpoison_out Uc memC (Z_to_bv 64 a) EU) in Hb.
        destruct (Hpr a (conj Hh (ex_intro _ b Hb))) as (_ & b' & Hb'). exists b'. exact Hb'. }
    split; [exact HP'|]. split; [exact H10'|].
    split; [intros i Hi; rewrite (Hset i Hi); reflexivity | exact Hfr'].
  - intros a [Ha | Ha].
    + left. right. right. left. exists P, N. split; [exact Hin|]. split; [exact Hnin|]. lia.
    + left. left. rewrite Rsp in Ha. lia. }
cbv beta. intros W' c' _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HARU2 & HP & H10' & HZ & HKEEP).
rewrite ERA.
apply (K regs2 mem2 md2 HJ2 HARU2 HP H10' HZ).
intros a0 H1 H2 H3. apply HKEEP; [exact H1 | exact H2 | rewrite Rsp; exact H3].
Qed.

(* ================= the step: pib_IM at __asan_memset -> segment G -> pib_IV at parse_value =================
   Route (A's pi_step_M on image B): piv_call_ms on the kid kids + 56 n (the kids block is a temporary block of the
   caller); pio_zero carries the open object, the key and the blocks to the memory after the memset; the resume state
   fss_retT 0x85170 144 pib_csL pib_rs pib_gfP under Ereg regs2 (fs_extraT ++ pib_xsK ...) (pivm_resumeT); the kit
   narrows it to pib_ss_G (every write window closed, pib_RL, the kid atom, its UBSan facts and alias); sh_ok for
   pib_SHm (piv_sh_q / piv_sh_v); the measured run pib_run_G (pivm_fin_G at its stop); the memory unchanged across it;
   pib_IV from the memset's facts and the stop registers. *)
Lemma piv_step_MG : forall dn kk x rm T lyc Sc Uc (W1 : world tfibsegs) memC mdC regsC chq pc kids keys cap Di Da
    peak1 a (Qc : world tfibsegs -> config -> Prop),
  IM dn kk x rm T lyc Sc Uc W1 memC mdC regsC chq pc kids keys cap Di Da peak1 a ->
  (forall mem' md' regs' chq',
     IV dn kk x rm T lyc Sc Uc W1 mem' md' regs' chq' pc kids keys cap Di Da peak1 a ->
     SRr tfibsegs W1 (YG0d.cfg_at tfibsegs A_parse_value regs' mem' md') Qc) ->
  SRr tfibsegs W1 (YG0d.cfg_at tfibsegs PC_memset regsC memC mdC) Qc.
Proof.
intros dn kk x rm T lyc Sc Uc W1 memC mdC regsC chq pc kids keys cap Di Da peak1 a Qc HIM K.
unfold pib_IM, pib_IK in HIM. cbv zeta in HIM.
destruct HIM as ((Hms & Htr & Hcap & Hcap54 & HJC & HRP & HFL & HSTK & HRS & HBL & HOBJ & HU64 & HCSTR) &
  R1 & R10 & R11 & R12).
pose proof HJC as (HJ & HARU & HRO & HHD).
pose proof HRP as (Rsp & R9 & R19 & R3 & R4 & RL).
pose proof HSTK as (HCH & HCHF & Htop & HINc & HWK).
pose proof HBL as (HTXc & HPOc & HBLKc & HPERM & HUc & HDa & HSUM & HLEN & HGL & Hpk).
pose proof HOBJ as (HHDR & HOPEN).
(* ---- the numbers ---- *)
pose proof asan_consts as (C1 & _).
pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof HARU as (HAR & _ & _).
pose proof (piv_sp0 B k ly S U W regs mem md ot ms ch Hk HPRE HDEP) as (Hsp16 & Hsp1 & Hsp2).
assert (HSTK2 : ESTACK + 144 <= STK_parse_items (1 - k))
  by (unfold STK_parse_items, STK_parse_items_of, zmaxl, FRAME_parse_items, STK_RT_INTRIN; cbn [fold_right]; lia).
assert (EST : ESTACK = 4096) by reflexivity.
assert (HH : HEAD = 16) by reflexivity.
pose proof (piv_v_rng B k ly S U W regs mem md v ch HPRE HPO0) as (Hv1 & Hv2).
pose proof (piv_q_stack B k ly S U W regs mem md q ot text len p tb ms ch Hk HPRE HWIN HQ16 HIN0 HDEP)
  as (Hqlo & Hqhi & Hq8 & Hqc & Hq47).
pose proof HWIN as (Hsq & Hq24 & Hot16 & Hotly & _).
pose proof HPRE as ((HAP & _ & _) & _). pose proof HAP as (_ & _ & _ & _ & _ & Hstk0 & _).
pose proof Hstk0 as (_ & _ & Hceil & Hslo & Hshi & H47 & _ & Htop1 & Htop2).
pose proof HJ as (_ & Hly & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Hlytop & Hlylo & Hlyhi & _).
pose proof HTX as (_ & (TIN0 & _) & _).
assert (Hn : Z.of_nat (length dn) < cap) by lia.
assert (ES : parse_items_shape.pis_slots true kids keys cap = [(kids, 56 * cap); (keys, 8 * cap)]).
{ unfold parse_items_shape.pis_slots, ReaderRes.kids_blk, ReaderRes.keys_blk.
  rewrite (proj2 (Z.eqb_neq cap 0)) by lia. reflexivity. }
assert (HinK : In (kids, 56 * cap)
  (parse_items_shape.pis_slots true kids keys cap ++ Di ++ [(a, Z.of_nat (length kk) + 1)]))
  by (apply in_or_app; left; rewrite ES; left; reflexivity).
assert (HinY : In (keys, 8 * cap)
  (parse_items_shape.pis_slots true kids keys cap ++ Di ++ [(a, Z.of_nat (length kk) + 1)]))
  by (apply in_or_app; left; rewrite ES; right; left; reflexivity).
assert (HinA : In (a, Z.of_nat (length kk) + 1)
  (parse_items_shape.pis_slots true kids keys cap ++ Di ++ [(a, Z.of_nat (length kk) + 1)]))
  by (apply in_or_app; right; apply in_or_app; right; left; reflexivity).
pose proof (HBLKc _ _ HinK) as KRB. pose proof KRB as (KIN & Kal & Kpos & _).
pose proof (HBLKc _ _ HinY) as YRB. pose proof YRB as (_ & Yal & _ & _).
pose proof (HBLKc _ _ HinA) as ARB.
destruct (fsw_rblock_low B lyc Sc W1 (unpoison Uc memC) mdC memC kids (56 * cap) HAR KRB) as (K1 & K2).
destruct (fsw_rblock_low B lyc Sc W1 (unpoison Uc memC) mdC memC keys (8 * cap) HAR YRB) as (KY1 & KY2).
destruct (fsw_rblock_low B lyc Sc W1 (unpoison Uc memC) mdC memC a _ HAR ARB) as (A1 & A2).
pose proof HTXc as (Htx0 & TRB & Htl). pose proof TRB as (TIN & _).
destruct (piv_text_rng B k S regs q ot text len tcap tb ms Hk HDEP lyc Sc W1 (unpoison Uc memC) mdC memC pc
  (Z.of_nat k + 1) HAR HTXc HINc) as (Tr1 & Tr2 & Tr3 & Tr4 & Tr5).
assert (Hreq : req_size (56 * cap + HEAD) = 56 * cap + HEAD) by (apply piv_req; lia).
assert (Hdk8 : (kids + 56 * Z.of_nat (length dn)) mod 8 = 0) by (clear - Kal; Z.div_mod_to_equations; lia).
assert (KNE : ~ In (kids - HEAD, 56 * cap + HEAD) (ablocks B ly S)).
{ apply (piv_not_entry B ly S lyc Sc W1 (unpoison Uc memC) mdC _ HAR HPERM).
  unfold rd_hblocks. exact (in_map (fun b1 => (fst b1 - HEAD, snd b1 + HEAD)) _ _ HinK). }
assert (Dkt : piv_hide (kids + 56 * cap <= text - HEAD \/ text + tcap <= kids - HEAD)).
{ assert (Hne : (kids - HEAD, 56 * cap + HEAD) <> (text - HEAD, tcap + HEAD)).
  { intros E. apply KNE. rewrite E. exact TIN0. }
  pose proof (sep_blocks tfibsegs B LAWS lyc Sc W1 _ mdC _ _ _ _ HAR KIN TIN Hne) as D.
  unfold zdisjoint in D. cbn [fst snd] in D. rewrite Hreq, (piv_req tcap) in D by lia. unfold piv_hide. lia. }
assert (Hxr : length xr = 13%nat) by (unfold xr; rewrite length_map; reflexivity).
(* ---- the call of __asan_memset (kids + 56 n, 0, 56) ---- *)
apply (piv_call_ms lyc Sc Uc W1 memC mdC (rd_ev T) regsC (kids + 56 * Z.of_nat (length dn)) (kids - HEAD)
  (56 * cap + HEAD) Qc HJC HRP R1 R10 R11 R12 KIN KNE ltac:(lia) ltac:(rewrite Hreq; lia)).
intros regs2 mem2 md2 HJ2 HARU2 HP H10' HZ HKEEP.
(* ---- the open object across the memset ---- *)
assert (HSC : alloc_ceiling <= spZ regs - 144 - ESTACK) by lia.
pose proof (pio_zero B ly S lyc Sc Uc W1 memC mem2 md2 (spZ regs - 144) v text len tcap (length dn) dn kids keys cap
  Di a kk eq_refl Hn HSC HARU2 ltac:(rewrite <- app_assoc; exact HPERM) ltac:(rewrite <- app_assoc; exact HBLKc)
  HTXc HPOc HHDR ltac:(rewrite <- app_assoc; exact HOPEN) HU64 ltac:(rewrite <- app_assoc; exact HCSTR) HKEEP) as Z0.
cbv zeta in Z0. rewrite <- app_assoc in Z0.
destruct Z0 as (BL5 & TX5 & PO5 & HDR5 & OP5 & U5 & C5).
(* ---- the resume env ---- *)
set (xs := pib_xsK pc (text + len) (Z.of_nat k + 1) xr kids keys (Z.of_nat (length dn)) cap a (Z.of_nat (length kk))).
destruct (pivm_xsK_nth pc (text + len) (Z.of_nat k + 1) xr kids keys (Z.of_nat (length dn)) cap a
  (Z.of_nat (length kk)) Hxr) as (X0 & X1 & X2 & XR & X16 & X17 & X18 & X19 & X20 & X21 & X23).
destruct (piv_env_at B k S regs q ot v ms Hk HDEP regsC regs2 xs pib_RL HRP HP) as (E9 & E19 & E32 & E2 & E3 & E4).
set (E := Ereg regs2 (fs_extraT ++ xs)) in *.
assert (EX : forall j, ew E (xatom j) = nth j xs (Z_to_bv 64 0)) by (intros j; unfold E; apply fsw_ew_xatom).
assert (Y0 : ew E (xatom 0) = Z_to_bv 64 pc) by (rewrite EX; exact X0).
assert (Y1 : ew E (xatom 1) = Z_to_bv 64 (text + len)) by (rewrite EX; exact X1).
assert (Y2 : ew E (xatom 2) = Z_to_bv 64 (Z.of_nat k + 1)) by (rewrite EX; exact X2).
assert (YR : forall j, (j < 13)%nat -> ew E (xatom (3 + j)) = nth j xr (Z_to_bv 64 0))
  by (intros j Hj; rewrite EX; exact (XR j Hj)).
assert (Y16 : ew E (xatom 16) = Z_to_bv 64 kids) by (rewrite EX; exact X16).
assert (Y17 : ew E (xatom 17) = Z_to_bv 64 keys) by (rewrite EX; exact X17).
assert (Y18 : ew E (xatom 18) = Z_to_bv 64 (Z.of_nat (length dn))) by (rewrite EX; exact X18).
assert (Y19 : ew E (xatom 19) = Z_to_bv 64 cap) by (rewrite EX; exact X19).
assert (Y20 : ew E (xatom 20) = Z_to_bv 64 a) by (rewrite EX; exact X20).
assert (Y21 : ew E (xatom 21) = Z_to_bv 64 (Z.of_nat (length kk))) by (rewrite EX; exact X21).
assert (Y23 : ew E (xatom 23) = Z_to_bv 64 (kids + 56 * Z.of_nat (length dn))) by (rewrite EX; exact X23).
assert (E9u : bv_unsigned (ew E 9) = q) by (rewrite E9; apply wz; lia).
assert (E19u : bv_unsigned (ew E 19) = v) by (rewrite E19; apply wz; lia).
(* ---- what the memset kept: every byte off the kid and off its stack window ---- *)
assert (NI : forall y, alloc_ceiling <= y -> ~ in_img tfibsegs y)
  by (intros y Hy Hi; pose proof (fs_segs_img y Hi); unfold FS_IMG_END in *; lia).
assert (KIMG : forall y, kids - HEAD <= y < kids + 56 * cap -> ~ in_img tfibsegs y)
  by (intros y Hy; apply (blk_img tfibsegs B LAWS lyc Sc W1 _ mdC _ _ y HAR KIN); rewrite Hreq; lia).
assert (RAW : forall y, 0 <= y < 2 ^ 64 -> ~ in_img tfibsegs y ->
   ~ (kids + 56 * Z.of_nat (length dn) <= y < kids + 56 * Z.of_nat (length dn) + 56) ->
   ~ (spZ regs - 144 - ESTACK <= y < spZ regs - 144) ->
   mrestrict (w_H W1) mem2 (Z_to_bv 64 y) = mrestrict (w_H W1) memC (Z_to_bv 64 y))
  by (intros y H1 H2 H3 H4; exact (fsw_restrict_of_aview (w_H W1) (w_H W1) memC mem2 y H1 H2 (HKEEP y H1 H3 H4))).
assert (MB : forall y, 0 <= y < 2 ^ 64 ->
   ~ (kids + 56 * Z.of_nat (length dn) <= y < kids + 56 * Z.of_nat (length dn) + 56) ->
   ~ (spZ regs - 144 - ESTACK <= y < spZ regs - 144) ->
   mbyte tfibsegs (rdW W1 mem2) y = mbyte tfibsegs (rdW W1 memC) y)
  by (intros y H1 H2 H3; exact (mbyte_of_aview tfibsegs _ _ _ _ y (HKEEP y H1 H2 H3))).
assert (FL2 : pib_frameL (rdW W1 mem2) (spZ regs) xr q v).
{ apply (pivm_frameL_mb (rdW W1 memC)); [|exact HFL]. intros y Hy. apply MB; lia. }
assert (HCS : Forall (YP09.chunk_ok tfibsegs E (rdW W1 mem2) (spZ regs - 144)) pib_csL)
  by exact (piv_csL_ok E _ (spZ regs) xr q v Hxr YR E9 E19 E32 ltac:(lia) ltac:(lia) ltac:(lia) FL2).
assert (HIN2 : PjIn.pj_in_ok tfibsegs (rdW W1 mem2) q text len pc (Z.of_nat k + 1) tb).
{ apply (pivm_in_keep (rdW W1 memC)); [exact HINc | |].
  - intros y Hy. apply RAW; [lia | apply NI; lia | lia | lia].
  - intros y Hy. apply RAW; [lia | | | lia].
    + apply (blk_img tfibsegs B LAWS lyc Sc W1 _ mdC _ _ y HAR TIN). rewrite (piv_req tcap) by lia. lia.
    + pose proof Dkt as D. unfold piv_hide in D. lia. }
assert (HG2 : fs_glob tfibsegs W1 mem2 (live + PjGrammar.held T) peak1 (cnt + Z.of_nat (length T)) fail).
{ apply (pim_glob_aview W1 W1 memC mem2); [|exact HGL].
  intros y Hy. pose proof (pim_pstat_img y Hy) as Hi. pose proof (fs_segs_img y Hi) as Hb.
  apply HKEEP; [unfold FS_IMG_END in *; lia | intros Hd; apply (KIMG y); [lia | exact Hi]
    | unfold FS_IMG_END in *; lia]. }
assert (RO2 : arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W1) mem2)).
{ apply (pim_ro_keep B (aview tfibsegs (w_H W1) memC)); [exact HRO|].
  intros y Hy. pose proof (fsw_roP_img y Hy) as Hi. pose proof (fs_segs_img y Hi) as Hb.
  apply HKEEP; [unfold FS_IMG_END in *; lia | intros Hd; apply (KIMG y); [lia | exact Hi]
    | unfold FS_IMG_END in *; lia]. }
assert (CH2 : achain lyc (aview tfibsegs (w_H W1) (unpoison Uc mem2)) (spZ regs) q chq).
{ apply (piv_chain_kept lyc lyc (aview tfibsegs (w_H W1) (unpoison Uc memC)) _ (spZ regs) q (ly_top ly) chq
    HCH HCHF Htop Htop).
  intros y Hy _. apply pivm_aview_unp. apply HKEEP; lia. }
assert (WK2 : wkeep tfibsegs W1 W1 memC mem2 (spZ regs) ot q 24).
{ intros y Hy Hq0.
  assert (Hraw : mrestrict (w_H W1) mem2 (Z_to_bv 64 y) = mrestrict (w_H W1) memC (Z_to_bv 64 y))
    by (apply RAW; [lia | apply NI; lia | lia | lia]).
  split; [exact (MB y ltac:(lia) ltac:(lia) ltac:(lia))|].
  split; intros Hw; [exact (writable_at_eq tfibsegs _ _ y Hraw Hw) | exact (writable_at_eq tfibsegs _ _ y (eq_sym Hraw) Hw)]. }
assert (WK : wkeep tfibsegs W W1 mem mem2 (spZ regs) ot q 24)
  by exact (piv_wkeep_trans k S W regs mem q ot ms Hk HDEP W1 W1 memC mem2 (spZ regs) HWK WK2 (Z.le_refl _)).
(* ---- the kid: zeroed, a placed object ---- *)
assert (ZB : forall y, kids + 56 * Z.of_nat (length dn) <= y < kids + 56 * Z.of_nat (length dn) + 56 ->
  mbyte tfibsegs (rdW W1 mem2) y = Some (Z_to_bv 8 0)).
{ intros y Hy. replace y with (kids + 56 * Z.of_nat (length dn) + (y - (kids + 56 * Z.of_nat (length dn)))) by lia.
  apply pivm_aview_some. apply HZ. lia. }
assert (KW2 : forall y, kids + 56 * Z.of_nat (length dn) <= y < kids + 56 * Z.of_nat (length dn) + 56 ->
  writable_at tfibsegs (rdW W1 mem2) y)
  by (intros y Hy; apply (pivm_blk_wr B lyc Sc Uc W1 mem2 md2 (kids - HEAD) (56 * cap + HEAD) y HARU2 KIN);
      rewrite Hreq; lia).
assert (HZ2 : PjStruct.pj_zero tfibsegs (rdW W1 mem2) (kids + 56 * Z.of_nat (length dn))).
{ split; [split; [exact Hdk8|]|].
  - split; [lia|]. split; [lia|]. intros y Hy. split; [exact (KW2 y Hy)|]. exists (Z_to_bv 8 0). exact (ZB y Hy).
  - split; [lia|]. split; [rewrite repeat_length; lia|]. intros i Hi. rewrite repeat_length in Hi.
    assert (Er : nth_error (repeat (Z_to_bv 8 0) 56) i = Some (Z_to_bv 8 0)) by (apply nth_error_repeat; exact Hi).
    rewrite Er. exact (ZB (kids + 56 * Z.of_nat (length dn) + Z.of_nat i) ltac:(lia)). }
assert (HPK2 : pobj tfibsegs B lyc Sc W1 mem2 (kids + 56 * Z.of_nat (length dn))).
{ split.
  - right. split; [exists (kids - HEAD), (56 * cap + HEAD); split; [exact KIN | rewrite Hreq; lia]|].
    split; [exact Hdk8|].
    exact (fsw_block_body_addressable B lyc Sc Uc W1 mem2 md2 (kids - HEAD) (56 * cap + HEAD)
      (kids + 56 * Z.of_nat (length dn)) 56 HARU2 HHD KIN
      ltac:(lia) ltac:(lia) ltac:(rewrite Hreq; lia)).
  - intros i Hi. apply KW2. lia. }
(* ---- the resume state at 0x85170 ---- *)
assert (Hv8 : v mod 8 = 0) by (destruct PO5 as [[(_ & Hm & _)|(_ & Hm & _)] _]; exact Hm).
assert (HRSOK : Forall (region_ok tfibsegs E (rdW W1 mem2)) pib_rs).
{ unfold pib_rs. constructor; [exact (pis_q_ok E _ q text len pc (Z.of_nat k + 1) tb E9u Y0 Y1 Y2 HIN2)|].
  constructor; [|constructor].
  exact (pivm_vR_ok E _ v kids keys (Z.of_nat (length dn)) cap E19u Y16 Y17 Y18 Y19 ltac:(lia) ltac:(lia)
    (proj2 PO5) HDR5). }
assert (Hvimg : piv_hide (v + 56 <= 0x10000 \/ FS_IMG_END <= v))
  by exact (fsw_pobj_off_img B lyc Sc W1 (unpoison Uc mem2) md2 mem2 v (proj1 HARU2) PO5).
assert (HPD : pairwise_disjoint E (fsT_ret_regions 144 pib_csL pib_rs))
  by exact (pivm_disj (rc:=rc) E (spZ regs) q v E2 E9u E19u ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hvimg).
assert (HGF : atoms_ok E pib_gfP).
{ apply (pivm_gfP_ok E q v pc (text + len) (Z.of_nat k + 1) kids keys (Z.of_nat (length dn)) cap a
    (Z.of_nat (length kk)) E9u E19u Y0 Y1 Y2 Y16 Y17 Y18 Y19 Y20 Y21); lia. }
assert (Usp2 : spZ regs2 = spZ regs - 144).
{ unfold spZ. rewrite (fsw_pres regsC regs2 2%bv HP ltac:(piv_acs)). exact Rsp. }
pose proof (pivm_resumeT B (STK_parse_items (1 - k) + (ot - spZ regs)) ot ([(v, v + 56)] ++ FS_PSTAT_FP) ly S W
  (unpoison U mem) md [] lyc Sc Uc W1 mem2 md2 (rd_ev T) regs2 (spZ regs) 144 xs pib_csL pib_rs pib_gfP 0x85170
  (proj1 HSS) (proj2 HSS) HJ2 HARU2 Usp2 ltac:(lia) ltac:(clear - Hsp16; Z.div_mod_to_equations; lia) ltac:(lia)
  ltac:(lia) pivm_ret_wf HCS HRSOK HPD HGF) as HST.
(* ---- segment G's start state pib_ss_G ---- *)
assert (S1 : st_ok tfibsegs E
  (pik_setm (fss_retT 0x85170 144 pib_csL pib_rs pib_gfP) (pib_rgs pib_csL pib_RO pib_RO pib_RO))
  (restrict (w_H W1) (mkst regs2 (Z_to_bv 64 0x85170) mem2 (seg_rom tfibsegs))))
  by exact (pik_st_ok_setm _ _ _ _ HST pivm_rgs_sub pivm_rgs_wf).
assert (Ha0 : YK11.getr regs2 10 = sv_denot E (SOff (xatom 23) 0)) by (rewrite fsw_SOff0, Y23, H10'; reflexivity).
pose proof (piv_setr_ok B k S regs q ot v ms Hk HDEP regsC regs2 xs pib_RL (SOff (xatom 23) 0) HRP HP piv_RL_ok Ha0)
  as FRL.
apply Forall_inv_tail in FRL.
assert (S3 : st_ok tfibsegs E
  (pik_setr (pik_setm (fss_retT 0x85170 144 pib_csL pib_rs pib_gfP) (pib_rgs pib_csL pib_RO pib_RO pib_RO)) pib_RL)
  (restrict (w_H W1) (mkst regs2 (Z_to_bv 64 0x85170) mem2 (seg_rom tfibsegs))))
  by (apply pik_st_ok_setr; [exact S1 | exact FRL]).
assert (HSm : st_ok tfibsegs E pib_ss_G (restrict (w_H W1) (mkst regs2 (Z_to_bv 64 0x85170) mem2 (seg_rom tfibsegs)))).
{ rewrite pivm_ss_G_is. apply pik_st_ok_addf; [exact S3 | | |].
  - apply (pivm_gf_vk E (kids + 56 * Z.of_nat (length dn)) Y23); [lia | exact Hdk8].
  - apply (pivm_conds E kids (Z.of_nat (length dn)) Y16 Y18 Y23); lia.
  - apply (pivm_al_vk E kids (Z.of_nat (length dn)) Y16 Y18 Y23); lia. }
(* ---- the shadow entries: q and v ---- *)
assert (UB : YP0e.U E fs_Bx = SHADOW_OFF) by (unfold fs_Bx; apply U_atom; [exact E32 | unfold SHADOW_OFF; lia]).
assert (Uq : YP0e.U E (SOff 9 0) = q) by (apply U_atom; [exact E9 | lia]).
assert (Uv : YP0e.U E (SOff 19 0) = v) by (apply U_atom; [exact E19 | lia]).
assert (SHOK : sh_ok tfibsegs fs_Bx pib_SHm E (rdW W1 mem2)).
{ unfold sh_ok, pib_SHm. constructor; [|constructor; [|constructor]].
  - exact (piv_sh_q B k ly S U W regs mem md q ot text len p tb ms ch Hk HPRE HWIN HQ16 HIN0 HDEP lyc Sc Uc W1 mem2 md2
      E 9 HARU2 Hlylo Hlyhi UB Uq).
  - exact (piv_sh_v B k S regs ot v ms Hk HDEP lyc Sc Uc W1 mem2 md2 E 19 HARU2 PO5 UB Uv). }
(* ---- the run G ---- *)
eapply (fsw_run_tok_AJU B pitems_tbl pitems_tbl_ok W1 FUEL _ (run_K 0 fs_Bx pib_SHm pib_ss_G) fs_Bx fs_Bspan pib_SHm
  pib_ss_G pib_st_G (TS_stopped SR_fetch) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HSm SHOK pib_static_G pib_run_G I
  HARU2 HJ2).
- destruct pivm_fin_G as (_ & Hob & _). rewrite Hob. constructor.
- intros a0 Ha0'. exfalso. exact (pivm_no_wr _ a0 Ha0').
- intros ws ms' mat' Hlen HS' SHOK' HJ' HARU' HFr HFr' HG'.
  destruct pivm_fin_G as (Hpc & Hob & Hresv & Hj & Hregs).
  rewrite Hj in Hlen. destruct ws as [|w ws]; [clear Hlen | discriminate Hlen].
  cbn [extK] in HS', SHOK'.
  assert (Emem : ms_mem ms' = mem2).
  { apply FunctionalExtensionality.functional_extensionality. intros y. apply HFr. exact (pivm_no_wr _ (bv_unsigned y)). }
  pose proof (st_ok_restrict_mkst tfibsegs (w_H W1) _ _ ms' HS' Hresv) as Hms'.
  pose proof (piv_regs_of_stop _ _ ms' (w_H W1) _ HS' Hregs) as RG. rewrite Forall_forall in RG.
  assert (G : forall r e, In (r, e) pivm_stopR -> YK11.getr (ms_regs ms') r = sv_denot E e)
    by (intros r e Hin; exact (RG (r, e) Hin)).
  pose proof (G 1%bv (SLit 0x851d0) ltac:(unfold pivm_stopR; apply in_or_app; left; cbn [In];
    repeat (first [left; reflexivity | right]))) as G1.
  pose proof (G 2%bv (SOff 2 0) ltac:(unfold pivm_stopR; apply in_or_app; left; cbn [In];
    repeat (first [left; reflexivity | right]))) as G2.
  pose proof (G 3%bv (SOff 3 0) ltac:(unfold pivm_stopR; apply in_or_app; left; cbn [In];
    repeat (first [left; reflexivity | right]))) as G3.
  pose proof (G 4%bv (SOff 4 0) ltac:(unfold pivm_stopR; apply in_or_app; left; cbn [In];
    repeat (first [left; reflexivity | right]))) as G4.
  pose proof (G 9%bv (SOff 9 0) ltac:(unfold pivm_stopR; apply in_or_app; left; cbn [In];
    repeat (first [left; reflexivity | right]))) as G9.
  pose proof (G 10%bv (SOff 9 0) ltac:(unfold pivm_stopR; apply in_or_app; left; cbn [In];
    repeat (first [left; reflexivity | right]))) as G10.
  pose proof (G 11%bv (SOff (xatom 23) 0) ltac:(unfold pivm_stopR; apply in_or_app; left; cbn [In];
    repeat (first [left; reflexivity | right]))) as G11.
  pose proof (G 19%bv (SOff 19 0) ltac:(unfold pivm_stopR; apply in_or_app; left; cbn [In];
    repeat (first [left; reflexivity | right]))) as G19.
  rewrite fsw_SOff0 in G2, G3, G4, G9, G10, G11, G19.
  rewrite Hms', Emem, Hpc. rewrite Emem in HJ', HARU'.
  apply (K mem2 (with_vm_backing (m_vm_lazy md2) mat' md2) (ms_regs ms') chq).
  unfold pib_IV, pib_IK. cbv zeta.
  split; [|split; [rewrite G1; reflexivity|split; [rewrite G10; exact E9|split; [rewrite G11, Y23; reflexivity|
    split; [exact HZ2 | exact HPK2]]]]].
  split; [exact Hms|]. split; [exact Htr|]. split; [exact Hcap|]. split; [exact Hcap54|].
  split; [split; [exact HJ'|]; split; [exact HARU'|]; split; [exact RO2 | exact HHD]|].
  split.
  { split; [unfold spZ; rewrite G2; exact E2|].
    split; [rewrite G9; exact E9|]. split; [rewrite G19; exact E19|].
    split; [rewrite G3; exact E3|]. split; [rewrite G4; exact E4|].
    apply (piv_RL_restate E (ms_regs ms'));
      [intros r e Hin; apply G; unfold pivm_stopR; apply in_or_app; right; exact Hin | reflexivity
      | symmetry; exact G9 | symmetry; exact G19 | exact E32]. }
  split; [exact FL2|].
  split; [split; [exact CH2|]; split; [exact HCHF|]; split; [exact Htop|]; split; [exact HIN2 | exact WK]|].
  split; [exact HRS|].
  split.
  { split; [exact TX5|]. split; [exact PO5|]. split; [exact BL5|]. split; [exact HPERM|]. split; [exact HUc|].
    split; [exact HDa|]. split; [exact HSUM|]. split; [exact HLEN|]. split; [exact HG2 | exact Hpk]. }
  split; [split; [exact HDR5 | exact OP5]|].
  split; [exact U5 | exact C5].
Qed.

(* ================= the call of parse_value (k + 1) on q and the kid, 0x851cc -> 0x851d0 ================= *)
Lemma piv_call_pv : forall dn kk x rm T lyc Sc Uc (W1 : world tfibsegs) memC mdC regsC chq pc kids keys cap Di Da
    peak1 a (Qc : world tfibsegs -> config -> Prop),
  IV dn kk x rm T lyc Sc Uc W1 memC mdC regsC chq pc kids keys cap Di Da peak1 a ->
  (forall D Dx ly' S' (W' : world tfibsegs) regs' mem' md',
     Permutation Dx D ->
     @ajournal rc SK tfibsegs B (STK_parse_value (1 - k) + (ot - spZ regsC)) ot
       ([(kids + 56 * Z.of_nat (length dn), kids + 56 * Z.of_nat (length dn) + 56)] ++ FS_PSTAT_FP)
       lyc Sc W1 (unpoison Uc memC) mdC [] ly' S' W' (unpoison (Uc ++ rd_heads Dx) mem') md'
       (rd_ev (PjRoundTrip.ttrace x)) ->
     upoison_ok B ly' S' (Uc ++ rd_heads Dx) -> upoisoned tfibsegs W' mem' (Uc ++ rd_heads Dx) ->
     aregs_preserved regsC regs' -> YK11.getr regs' 10 = w64 0 ->
     PjIn.pj_in_ok tfibsegs (rdW W' mem') q text len
       (pc + Z.of_nat (length (if pr then [32] else [])) +
        Z.of_nat (length (concat (WriterValue.wvpieces x pr (Z.of_nat k + 1))))) (Z.of_nat k + 1) tb ->
     wkeep tfibsegs W1 W' memC mem' (spZ regsC) ot q 24 ->
     Permutation (ablocks B ly' S') (ablocks B lyc Sc ++ rd_hblocks D) ->
     rtree tfibsegs B ly' S' W' mem' (kids + 56 * Z.of_nat (length dn)) x D ->
     rd_sum D = PjGrammar.held (PjRoundTrip.ttrace x) ->
     (length D <= length (PjRoundTrip.ttrace x))%nat ->
     pobj tfibsegs B ly' S' W' mem' (kids + 56 * Z.of_nat (length dn)) ->
     rd_text tfibsegs B ly' S' W' mem' text len tcap ->
     (exists peak', peak1 <= peak' /\
        fs_glob tfibsegs W' mem' (live + PjGrammar.held T + PjGrammar.held (PjRoundTrip.ttrace x)) peak'
          (cnt + Z.of_nat (length T) + Z.of_nat (length (PjRoundTrip.ttrace x))) fail) ->
     SRr tfibsegs W' (mkCfg (mkst regs' (Z_to_bv 64 0x851d0) mem' (seg_rom tfibsegs)) md') Qc) ->
  SRr tfibsegs W1 (YG0d.cfg_at tfibsegs A_parse_value regsC memC mdC) Qc.
Proof.
intros dn kk x rm T lyc Sc Uc W1 memC mdC regsC chq pc kids keys cap Di Da peak1 a Qc HIV K.
unfold pib_IV, pib_IK in HIV. cbv zeta in HIV.
destruct HIV as ((Hms & Htr & Hcap & Hcap54 & HJC & HRP & HFL & HSTK & HTXT & HBL & HOBJ & Hu64 & Hcstr) &
  R1 & R10 & R11 & HZK & HPK).
pose proof HJC as (HJ & HARU & HRO & HHD).
pose proof HRP as (Rsp & R9 & R19 & R3 & R4 & RL).
pose proof HSTK as (HCH & HFW & Htop & HIN & HWK).
pose proof HBL as (HTX1 & HPO1 & HRB & HPERM & HUc & HDa & HSUM & HLEN & HG1 & Hpk).
pose proof HOBJ as (HHDR & HOP).
pose proof HARU as (HAR & _ & _).
pose proof asan_consts as (C1 & _ & C3 & _).
pose proof (AR_laws_ok tfibsegs B) as LAWS.
assert (EkS : Z.of_nat (Datatypes.S k) = Z.of_nat k + 1) by lia.
(* ---- the numbers of the entry ---- *)
pose proof (piv_sp0 B k ly S U W regs mem md ot ms ch Hk HPRE HDEP) as (Hsp16 & Hsp1 & Hsp2).
pose proof (piv_stk144 k S regs ot ms Hk HDEP) as H144.
pose proof (piv_v_rng B k ly S U W regs mem md v ch HPRE HPO0) as (Hv1 & Hv2).
pose proof (piv_q_stack B k ly S U W regs mem md q ot text len p tb ms ch Hk HPRE HWIN HQ16 HIN0 HDEP)
  as (Hqlo & Hqhi & Hq8 & Hqc & Hq47).
pose proof HWIN as (Hsq & Hq24 & Hot16 & Hotly & _).
pose proof HJ as (_ & Hly & _ & _ & _ & _ & Hnev & _ & _ & _ & _ & _ & _ & Hpres & Hstkj & _).
pose proof HTX as (_ & TRB0 & _). pose proof TRB0 as (TIN0 & _).
assert (HH : HEAD = 16) by reflexivity.
assert (Hn : Z.of_nat (length dn) < cap) by lia.
pose proof Hstkj as (_ & _ & Hclo & Hlos & Hoths & Hshi2 & _ & Hotltop & _).
assert (Hot47 : ot <= 2 ^ 47) by lia.
assert (HSTKv : STK_parse_value (1 - k) + 144 <= STK_parse_items (1 - k))
  by (unfold STK_parse_items, STK_parse_items_of, zmaxl, FRAME_parse_items; cbn [fold_right]; lia).
assert (HSTK0 : 0 <= STK_parse_value (1 - k))
  by (destruct (1 - k)%nat; cbn [STK_parse_value]; unfold PROBE_parse_value, PROBE_PAGE; lia).
(* ---- the member's own facts, the budgets, the frames ---- *)
destruct (piv_mem_facts k S regs ot ms Hk HDV HDS HWF HDEP dn kk x rm Hms) as (Hplain & Hsoo & Hstr & Hwf & Hdep).
destruct (piv_budget B k ly S regs ot ms live cnt fail Hk HQT HSZ HLIVE HEV HBB HDEP lyc Sc
  (parse_items_shape.pis_slots true kids keys cap ++ Di ++ [(a, Z.of_nat (length kk) + 1)]) T
  (PjRoundTrip.ttrace x) (PjRoundTrip.tgo_obj (Datatypes.S (length dn)) (Z.to_nat cap) rm)
  Htr Hnev HPERM HSUM HLEN) as (B1 & B2 & B3 & B4 & B5).
assert (HFRL1 : Z.of_nat (length (frames Sc)) <= FRL_parse_value (Z.of_nat (Datatypes.S k))).
{ rewrite (piv_frames B k ly S U W regs mem md ot v lyc Sc Uc W1 memC mdC (rd_ev T) HJC).
  rewrite EkS. exact HFRL. }
(* ---- the kids / keys blocks of v, and the kid ---- *)
assert (Eslots : parse_items_shape.pis_slots true kids keys cap = [(kids, 56 * cap); (keys, 8 * cap)]).
{ unfold parse_items_shape.pis_slots, ReaderRes.kids_blk, ReaderRes.keys_blk, parse_items_shape.pis_oz.
  rewrite (proj2 (Z.eqb_neq cap 0)) by lia. cbn [Z.add Z.eqb negb orb app]. reflexivity. }
assert (KinL : In (kids, 56 * cap)
  (parse_items_shape.pis_slots true kids keys cap ++ Di ++ [(a, Z.of_nat (length kk) + 1)]))
  by (apply in_or_app; left; rewrite Eslots; left; reflexivity).
assert (YinL : In (keys, 8 * cap)
  (parse_items_shape.pis_slots true kids keys cap ++ Di ++ [(a, Z.of_nat (length kk) + 1)]))
  by (apply in_or_app; left; rewrite Eslots; right; left; reflexivity).
assert (AinL : In (a, Z.of_nat (length kk) + 1)
  (parse_items_shape.pis_slots true kids keys cap ++ Di ++ [(a, Z.of_nat (length kk) + 1)]))
  by (apply in_or_app; right; apply in_or_app; right; left; reflexivity).
pose proof (HRB _ _ KinL) as KRB. pose proof (HRB _ _ YinL) as YRB. pose proof (HRB _ _ AinL) as ARB.
pose proof KRB as (KIN & Kal & _ & _). pose proof YRB as (YIN & Yal & _ & _). pose proof ARB as (AIN & Aal & _ & _).
destruct (fsw_rblock_low B lyc Sc W1 (unpoison Uc memC) mdC memC kids _ HAR KRB) as (KL1 & KL2).
destruct (fsw_rblock_low B lyc Sc W1 (unpoison Uc memC) mdC memC keys _ HAR YRB) as (YL1 & YL2).
destruct (fsw_rblock_low B lyc Sc W1 (unpoison Uc memC) mdC memC a _ HAR ARB) as (AL1 & AL2).
pose proof HTX1 as (Ht0 & TRB & Htl). pose proof TRB as (TIN & _).
destruct (fsw_rblock_low B lyc Sc W1 (unpoison Uc memC) mdC memC text tcap HAR TRB) as (T1 & T2).
pose proof (PjIn.pj_in_ok_bounds tfibsegs _ _ _ _ _ _ _ HIN) as (Bq0 & Bq24 & Bt0 & Bpc & Btl & Bqt & Blen & Bq8 & Bd).
(* v is apart from the kids and the keys blocks (the open object's pj_apart) *)
pose proof HOP as (_ & HAPs & _).
assert (Dvk : forall z, kids <= z < kids + 56 * cap -> ~ (v <= z < v + 56)).
{ intros z Hz. apply (HAPs (kids, 56 * cap) z); [apply in_or_app; left; rewrite Eslots; left; reflexivity|].
  unfold PjStruct.pj_holds. cbn [fst snd]. lia. }
(* the kids block is no block of the entry, so it is apart from the text block *)
assert (Ktmp : ~ In (kids - HEAD, 56 * cap + HEAD) (ablocks B ly S)).
{ apply (piv_not_entry B ly S lyc Sc W1 (unpoison Uc memC) mdC _ HAR HPERM).
  unfold rd_hblocks. apply (in_map (fun b => (fst b - HEAD, snd b + HEAD)) _ _ KinL). }
assert (Ytmp : ~ In (keys - HEAD, 8 * cap + HEAD) (ablocks B ly S)).
{ apply (piv_not_entry B ly S lyc Sc W1 (unpoison Uc memC) mdC _ HAR HPERM).
  unfold rd_hblocks. apply (in_map (fun b => (fst b - HEAD, snd b + HEAD)) _ _ YinL). }
assert (Dkt : piv_hide (kids + 56 * cap <= text - HEAD \/ text + tcap <= kids - HEAD)).
{ assert (Hne : (kids - HEAD, 56 * cap + HEAD) <> (text - HEAD, tcap + HEAD))
    by (intros E; apply Ktmp; rewrite E; exact TIN0).
  pose proof (sep_blocks tfibsegs B LAWS lyc Sc W1 _ mdC _ _ _ _ HAR KIN TIN Hne) as Dd.
  unfold zdisjoint in Dd. cbn [fst snd] in Dd. rewrite !piv_req in Dd by lia. unfold piv_hide. lia. }
assert (Dky : piv_hide (kids + 56 * cap <= keys - HEAD \/ keys + 8 * cap <= kids - HEAD)).
{ assert (Hne : (kids - HEAD, 56 * cap + HEAD) <> (keys - HEAD, 8 * cap + HEAD))
    by (intros E; injection E as _ E2; lia).
  pose proof (sep_blocks tfibsegs B LAWS lyc Sc W1 _ mdC _ _ _ _ HAR KIN YIN Hne) as Dd.
  unfold zdisjoint in Dd. cbn [fst snd] in Dd. rewrite !piv_req in Dd by lia. unfold piv_hide. lia. }
(* ---- parse_value's fpreU: the chain at s0 = q + 16 (image B) ---- *)
assert (E9c : ew (Ereg regsC fs_extraT) 9 = Z_to_bv 64 q)
  by (rewrite (ew_Ereg_nat regsC fs_extraT 9 9%bv eq_refl); exact R9).
assert (R8 : YK11.getr regsC 8 = w64 (q + 16)).
{ rewrite Forall_forall in RL. pose proof (RL (8%bv, SOff 9 16) ltac:(unfold pib_RL; cbn [In]; tauto)) as H8.
  cbn [fst snd] in H8. rewrite H8.
  exact (piv_den_off (Ereg regsC fs_extraT) 9 q 16 E9c ltac:(lia) ltac:(lia) ltac:(lia)). }
assert (Es0 : s0Z regsC = q + 16) by (unfold s0Z; rewrite R8; unfold w64; apply wz; lia).
assert (HCH1 : exists ch1, achain lyc (aview tfibsegs (w_H W1) (unpoison Uc memC)) (spZ regsC) (s0Z regsC) ch1).
{ rewrite Es0. destruct (pis_in_vals (rdW W1 memC) q text len pc (Z.of_nat k + 1) tb HIN) as (Vp & Ve).
  apply (pim_chain_q16 lyc _ (spZ regsC) q (text + len) pc).
  - rewrite (pim_rdword_U B lyc Sc Uc W1 memC mdC (q + 8) HARU) by lia.
    exact (YF0x.val_mem_rdword (w_H W1) memC (q + 8) (text + len) ltac:(lia) Ve).
  - rewrite (pim_rdword_U B lyc Sc Uc W1 memC mdC q HARU) by lia.
    exact (YF0x.val_mem_rdword (w_H W1) memC q pc ltac:(lia) Vp).
  - unfold HEAD in *. lia.
  - lia.
  - exact Hq8.
  - lia. }
destruct HCH1 as [ch1 HCH1].
assert (PRE : fpreU tfibsegs B (STK_parse_value (1 - k)) lyc Sc Uc W1 regsC memC mdC ch1).
{ apply (fsw_fpreU_atFP B (STK_parse_items (1 - k) + (ot - spZ regs)) ot ([(v, v + 56)] ++ FS_PSTAT_FP) ly S Uc W
    (unpoison U mem) md [] lyc Sc W1 memC mdC (rd_ev T) regsC (STK_parse_value (1 - k))
    (spZ regs - 144 - ot) ch1 HJ HARU HRO).
  - rewrite Rsp. lia.
  - clear - Hsp16 Hot16. Z.div_mod_to_equations. lia.
  - lia.
  - exact HSTK0.
  - lia.
  - rewrite R1. unfold YK0s.ret_ok. vm_compute. reflexivity.
  - unfold raZ. rewrite R1. unfold w64. rewrite wz by lia. lia.
  - exact R3.
  - exact R4.
  - exact HCH1. }
assert (HWINc : rd_win tfibsegs regsC lyc W1 memC q ot).
{ unfold rd_win. rewrite Rsp. split; [lia|]. split; [lia|]. split; [exact Hot16|].
  split; [rewrite Htop; exact Hotly|].
  intros a0 Ha0. apply (fsw_apresent_unpoison B lyc Sc Uc W1 memC mdC a0 HARU).
  - clear - Ha0 C1 C3 Hsp1 H144 Hot47. lia.
  - apply Hpres. lia. }
(* ---- the call ---- *)
eapply SRr_bind.
{ apply (HPV lyc Sc Uc W1 regsC memC mdC ch1 q ot (kids + 56 * Z.of_nat (length dn)) text len pc tb tcap x pr
    (if pr then [32] else [])
    (concat (pi_mgo pr (Z.of_nat k) (Datatypes.S (length dn)) rm) ++ pib_wsb pr (Z.of_nat k) ++ [125] ++ rest)
    (live + PjGrammar.held T) peak1 (cnt + Z.of_nat (length T)) fail).
  - lia.
  - change (2 - Datatypes.S k)%nat with (1 - k)%nat. exact PRE.
  - exact HHD.
  - exact HFRL1.
  - exact R10.
  - exact R11.
  - rewrite EkS. exact HIN.
  - exact HWINc.
  - right. split; [rewrite Rsp; lia|]. exists chq. split.
    + apply (achain_lower lyc _ (spZ regs) (spZ regsC) q chq HCH). rewrite Rsp. lia.
    + rewrite Htop. exact HFW.
  - exact HTX1.
  - rewrite EkS. exact HTXT.
  - exact (pim_wsep_ws pr).
  - exact Hsoo.
  - exact Hstr.
  - exact Hwf.
  - exact Hdep.
  - exact HPK.
  - exact HZK.
  - change (2 - Datatypes.S k)%nat with (1 - k)%nat. left. rewrite Rsp. lia.
  - unfold piv_hide in *. clear - Dkt Hn KL1 KL2 T1 T2 HH. lia.
  - exact HG1.
  - exact B1.
  - exact B5.
  - exact B2.
  - exact B3.
  - exact B4. }
cbv beta. intros W' c' _ (D & Da2 & HPm & ly' & S' & regs' & mem' & md' & -> & HJc & OK' & PO' & HP &
  (A0 & HIN' & HWK' & HPERM' & HRT & HSUMx & HLENx & HPOk & HTX' & HG')).
change (2 - Datatypes.S k)%nat with (1 - k)%nat in HJc.
rewrite EkS in HIN'.
rewrite R1.
exact (K D Da2 ly' S' W' regs' mem' md' HPm HJc OK' PO' HP A0 HIN' HWK' HPERM' HRT HSUMx HLENx HPOk HTX' HG').
Qed.

(* ---- a live reader block across the callee's journal, its 8-byte head off the footprint ---- *)
Lemma piv_rblock_kept : forall STK1 sp1 FP1 ly1 S1 U1 (Wc : world tfibsegs) mc mdc ly2 S2 U2 (W2 : world tfibsegs)
    m2 md2 kc p0 n0,
  @ajournal rc SK tfibsegs B STK1 sp1 FP1 ly1 S1 Wc (unpoison U1 mc) mdc [] ly2 S2 W2 (unpoison U2 m2) md2 kc ->
  ARU tfibsegs B ly1 S1 U1 Wc mc mdc -> upoison_ok B ly2 S2 U2 -> upoisoned tfibsegs W2 m2 U2 ->
  (forall z, p0 - HEAD <= z < p0 - HEAD + 8 -> ~ inFP FP1 z) ->
  fs_rblock tfibsegs B ly1 S1 Wc mc p0 n0 -> fs_rblock tfibsegs B ly2 S2 W2 m2 p0 n0.
Proof.
intros STK1 sp1 FP1 ly1 S1 U1 Wc mc mdc ly2 S2 U2 W2 m2 md2 kc p0 n0 HJ1 HU1 OK2 PO2 HF (Hin & Hal & Hn0 & Hv).
assert (Hr : req_size (n0 + HEAD) = n0 + HEAD) by (apply pio_req_hb; lia).
split; [|split; [exact Hal | split; [exact Hn0|]]].
- apply (fsw_journal_block_live B STK1 sp1 FP1 ly1 S1 Wc (unpoison U1 mc) mdc ly2 S2 W2 (unpoison U2 m2) md2 kc
    (p0 - HEAD) (n0 + HEAD) (p0 - HEAD) HJ1 Hin); [unfold HEAD in *; lia | apply HF; unfold HEAD in *; lia].
- intros j Hj.
  assert (Eb : mrestrict (w_H W2) m2 (Z_to_bv 64 (p0 - HEAD + Z.of_nat j)) =
               mrestrict (w_H Wc) mc (Z_to_bv 64 (p0 - HEAD + Z.of_nat j))).
  { refine (proj2 (fsw_journal_kept_byte B STK1 sp1 FP1 ly1 S1 U1 Wc mc mdc ly2 S2 U2 W2 m2 md2 kc _
      HJ1 HU1 OK2 PO2 _ _)).
    - left. exists (p0 - HEAD), (n0 + HEAD). split; [exact Hin|]. try (cbn in Hj). unfold HEAD in *. lia.
    - apply HF. try (cbn in Hj). lia. }
  unfold mbyte. rewrite Eb. exact (Hv j Hj).
Qed.

(* ================= the step: pib_IV at the call -> pib_IH at the resume 0x851d0 ================= *)
Lemma piv_step_V : forall dn kk x rm T lyc Sc Uc (W1 : world tfibsegs) memC mdC regsC chq pc kids keys cap Di Da
    peak1 a (Qc : world tfibsegs -> config -> Prop),
  IV dn kk x rm T lyc Sc Uc W1 memC mdC regsC chq pc kids keys cap Di Da peak1 a ->
  (forall D Dx ly' S' (W' : world tfibsegs) regs' mem' md',
     IH dn kk x rm T lyc Sc Uc W1 memC mdC regsC chq pc kids keys cap Di Da peak1 a D Dx ly' S' W' regs' mem' md' ->
     SRr tfibsegs W' (mkCfg (mkst regs' (Z_to_bv 64 0x851d0) mem' (seg_rom tfibsegs)) md') Qc) ->
  SRr tfibsegs W1 (YG0d.cfg_at tfibsegs A_parse_value regsC memC mdC) Qc.
Proof.
intros dn kk x rm T lyc Sc Uc W1 memC mdC regsC chq pc kids keys cap Di Da peak1 a Qc HIV K.
pose proof HIV as HIV0. unfold pib_IV, pib_IK in HIV0. cbv zeta in HIV0.
destruct HIV0 as ((Hms & Htr & Hcap & Hcap54 & HJC & HRP & HFL & HSTK & HTXT & HBL & HOBJ & Hu64 & Hcstr) &
  R1 & R10 & R11 & HZK & HPK).
pose proof HJC as (HJ & HARU & HRO & HHD).
pose proof HRP as (Rsp & R9 & R19 & R3 & R4 & RL).
pose proof HSTK as (HCH & HFW & Htop & HIN & HWK).
pose proof HBL as (HTX1 & HPO1 & HRB & HPERM & HUc & HDa & HSUM & HLEN & HG1 & Hpk).
pose proof HOBJ as (HHDR & HOP).
pose proof HARU as (HAR & _ & _).
pose proof asan_consts as (C1 & _ & C3 & _).
pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstkj & _).
pose proof (piv_sp0 B k ly S U W regs mem md ot ms ch Hk HPRE HDEP) as (Hsp16 & Hsp1 & Hsp2).
pose proof (piv_stk144 k S regs ot ms Hk HDEP) as H144.
pose proof (piv_v_rng B k ly S U W regs mem md v ch HPRE HPO0) as (Hv1 & Hv2).
pose proof (piv_q_stack B k ly S U W regs mem md q ot text len p tb ms ch Hk HPRE HWIN HQ16 HIN0 HDEP)
  as (Hqlo & Hqhi & Hq8 & Hqc & Hq47).
pose proof HWIN as (Hsq & Hq24 & Hot16 & Hotly & _).
pose proof Hstkj as (_ & _ & Hclo & Hlos & Hoths & Hshi2 & _ & Hotltop & _).
assert (Hot47 : ot <= 2 ^ 47) by lia.
assert (HH : HEAD = 16) by reflexivity.
assert (Hn : Z.of_nat (length dn) < cap) by lia.
assert (Hv8 : v mod 8 = 0) by (destruct HPO1 as [[(_ & Hm & _)|(_ & Hm & _)] _]; exact Hm).
assert (Hvimg : piv_hide (v + 56 <= 0x10000 \/ FS_IMG_END <= v)).
{ pose proof HPRE as ((HAP0 & _ & _) & _). pose proof HAP0 as (HAR0 & _).
  exact (fsw_pobj_off_img B ly S W (unpoison U mem) md mem v HAR0 HPO0). }
assert (HSTKv : STK_parse_value (1 - k) + 144 <= STK_parse_items (1 - k))
  by (unfold STK_parse_items, STK_parse_items_of, zmaxl, FRAME_parse_items; cbn [fold_right]; lia).
assert (HSTK0 : 0 <= STK_parse_value (1 - k))
  by (destruct (1 - k)%nat; cbn [STK_parse_value]; unfold PROBE_parse_value, PROBE_PAGE; lia).
(* ---- the kids / keys / key blocks of the open object ---- *)
assert (Eslots : parse_items_shape.pis_slots true kids keys cap = [(kids, 56 * cap); (keys, 8 * cap)]).
{ unfold parse_items_shape.pis_slots, ReaderRes.kids_blk, ReaderRes.keys_blk, parse_items_shape.pis_oz.
  rewrite (proj2 (Z.eqb_neq cap 0)) by lia. cbn [Z.add Z.eqb negb orb app]. reflexivity. }
assert (Eblk : ReaderRes.kids_blk kids cap ++ ReaderRes.keys_blk 6 keys cap = [(kids, 56 * cap); (keys, 8 * cap)]).
{ unfold ReaderRes.kids_blk, ReaderRes.keys_blk. rewrite (proj2 (Z.eqb_neq cap 0)) by lia.
  cbn [Z.eqb negb orb app]. reflexivity. }
assert (KinL : In (kids, 56 * cap)
  (parse_items_shape.pis_slots true kids keys cap ++ Di ++ [(a, Z.of_nat (length kk) + 1)]))
  by (apply in_or_app; left; rewrite Eslots; left; reflexivity).
assert (YinL : In (keys, 8 * cap)
  (parse_items_shape.pis_slots true kids keys cap ++ Di ++ [(a, Z.of_nat (length kk) + 1)]))
  by (apply in_or_app; left; rewrite Eslots; right; left; reflexivity).
assert (AinL : In (a, Z.of_nat (length kk) + 1)
  (parse_items_shape.pis_slots true kids keys cap ++ Di ++ [(a, Z.of_nat (length kk) + 1)]))
  by (apply in_or_app; right; apply in_or_app; right; left; reflexivity).
pose proof (HRB _ _ KinL) as KRB. pose proof (HRB _ _ YinL) as YRB. pose proof (HRB _ _ AinL) as ARB.
pose proof KRB as (KIN & Kal & _ & _). pose proof YRB as (YIN & Yal & _ & _). pose proof ARB as (AIN & Aal & _ & _).
destruct (fsw_rblock_low B lyc Sc W1 (unpoison Uc memC) mdC memC kids _ HAR KRB) as (KL1 & KL2).
destruct (fsw_rblock_low B lyc Sc W1 (unpoison Uc memC) mdC memC keys _ HAR YRB) as (YL1 & YL2).
destruct (fsw_rblock_low B lyc Sc W1 (unpoison Uc memC) mdC memC a _ HAR ARB) as (AL1 & AL2).
pose proof HOP as (_ & HAPs & _).
assert (Dvk : forall z, kids <= z < kids + 56 * cap -> ~ (v <= z < v + 56)).
{ intros z Hz. apply (HAPs (kids, 56 * cap) z); [apply in_or_app; left; rewrite Eslots; left; reflexivity|].
  unfold PjStruct.pj_holds. cbn [fst snd]. lia. }
assert (Dky : piv_hide (kids + 56 * cap <= keys - HEAD \/ keys + 8 * cap <= kids - HEAD)).
{ assert (Hne : (kids - HEAD, 56 * cap + HEAD) <> (keys - HEAD, 8 * cap + HEAD))
    by (intros Ee; injection Ee as _ Ee2; lia).
  pose proof (sep_blocks tfibsegs B LAWS lyc Sc W1 _ mdC _ _ _ _ HAR KIN YIN Hne) as Dd.
  unfold zdisjoint in Dd. cbn [fst snd] in Dd. rewrite !piv_req in Dd by lia. unfold piv_hide. lia. }
assert (Ktmp : ~ In (kids - HEAD, 56 * cap + HEAD) (ablocks B ly S)).
{ apply (piv_not_entry B ly S lyc Sc W1 (unpoison Uc memC) mdC _ HAR HPERM).
  unfold rd_hblocks. apply (in_map (fun b => (fst b - HEAD, snd b + HEAD)) _ _ KinL). }
(* ---- the call ---- *)
apply (piv_call_pv dn kk x rm T lyc Sc Uc W1 memC mdC regsC chq pc kids keys cap Di Da peak1 a Qc HIV).
intros D Dx ly' S' W' regs' mem' md' HPm HJc OK' PO' HP A0 HIN' HWK' HPERM' HRT HSUMx HLENx HPOk HTX' HG'.
set (vk := kids + 56 * Z.of_nat (length dn)) in *.
set (p' := pc + Z.of_nat (length (if pr then [32] else [])) +
           Z.of_nat (length (concat (WriterValue.wvpieces x pr (Z.of_nat k + 1))))) in *.
assert (HARU' : ARU tfibsegs B ly' S' (Uc ++ rd_heads Dx) W' mem' md')
  by (split; [exact (proj1 HJc) | split; [exact OK' | exact PO']]).
pose proof HARU' as (HAR' & _ & _).
assert (Hvk1 : kids <= vk) by (unfold vk; lia).
assert (Hvk2 : vk + 56 <= kids + 56 * cap) by (unfold vk; lia).
(* ---- what parse_value kept: every block / frame byte of the call off the kid ---- *)
assert (NFPk : forall z, ~ (vk <= z < vk + 56) -> ~ inFP FS_PSTAT_FP z ->
  ~ inFP ([(vk, vk + 56)] ++ FS_PSTAT_FP) z) by (intros z Hz1 Hz2; exact (pio_inFP_kid vk z Hz1 Hz2)).
assert (VB : forall z, v <= z < v + 56 ->
  mrestrict (w_H W') mem' (Z_to_bv 64 z) = mrestrict (w_H W1) memC (Z_to_bv 64 z)).
{ intros z Hz.
  refine (proj2 (fsw_journal_kept_byte B _ _ _ lyc Sc Uc W1 memC mdC ly' S' _ W' mem' md' _ z HJc HARU OK' PO' _ _)).
  - destruct HPO1 as [[((cid & pos & Hin & Hc8 & H8 & Hb1 & Hb2) & _)|((b0 & m0 & Hb0 & Hb1 & Hb2) & _)] _].
    + right. exists cid, pos. split; [exact Hin | lia].
    + left. exists b0, m0. split; [exact Hb0 | lia].
  - apply NFPk.
    + intros Hc. apply (Dvk z ltac:(lia)). lia.
    + exact (proj1 (proj2 (proj2 (pio_v_geo B lyc Sc W1 (unpoison Uc memC) mdC memC v z HAR HPO1 Hz)))). }
assert (VBm : forall y, v <= y < v + 56 ->
  mbyte tfibsegs (mrestrict (w_H W') mem') y = mbyte tfibsegs (mrestrict (w_H W1) memC) y)
  by (intros y Hy; unfold mbyte; rewrite (VB y Hy); reflexivity).
assert (HHDR' : PjStruct.pj_hdr tfibsegs (mrestrict (w_H W') mem') v 6 0 0 kids keys (Z.of_nat (length dn)) cap).
{ apply (PjStruct.pj_hdr_eq tfibsegs (mrestrict (w_H W1) memC)); [exact HHDR|].
  intros z Hz. exact (piv_word_eq _ _ (fun y => v <= y < v + 56) z VB Hz). }
assert (VW' : forall i, 0 <= i < 56 -> writable_at tfibsegs (mrestrict (w_H W') mem') (v + i))
  by (intros i Hi; apply (writable_at_eq tfibsegs (mrestrict (w_H W1) memC));
      [exact (VB (v + i) ltac:(lia)) | exact (proj2 HPO1 i Hi)]).
assert (KBr : forall P N z, In (P, N) (ablocks B lyc Sc) -> P <= z < P + req_size N -> ~ (vk <= z < vk + 56) ->
  mrestrict (w_H W') mem' (Z_to_bv 64 z) = mrestrict (w_H W1) memC (Z_to_bv 64 z)).
{ intros P N z Hin Hr Hz2.
  refine (proj2 (fsw_journal_kept_byte B _ _ _ lyc Sc Uc W1 memC mdC ly' S' _ W' mem' md' _ z HJc HARU OK' PO'
    (or_introl (ex_intro _ P (ex_intro _ N (conj Hin Hr)))) _)).
  apply NFPk; [exact Hz2
    | exact (proj1 (proj2 (proj2 (pio_blk_geo B lyc Sc W1 (unpoison Uc memC) mdC P N z HAR Hin Hr))))]. }
assert (KBm : forall y, kids <= y < kids + 56 * cap \/ keys <= y < keys + 8 * cap -> ~ (vk <= y < vk + 56) ->
  mbyte tfibsegs (mrestrict (w_H W') mem') y = mbyte tfibsegs (mrestrict (w_H W1) memC) y).
{ intros y Hy Hz2. unfold mbyte. destruct Hy as [Hy|Hy].
  - rewrite (KBr (kids - HEAD) (56 * cap + HEAD) y KIN ltac:(rewrite piv_req by lia; lia) Hz2). reflexivity.
  - rewrite (KBr (keys - HEAD) (8 * cap + HEAD) y YIN ltac:(rewrite piv_req by lia; lia) Hz2). reflexivity. }
assert (BLK' : rd_blocks_ok tfibsegs B ly' S' W' mem' (ReaderRes.kids_blk kids cap ++ ReaderRes.keys_blk 6 keys cap)).
{ intros a0 k0 Hak. rewrite Eblk in Hak. destruct Hak as [Eq|[Eq|[]]]; injection Eq as <- <-.
  - apply (piv_rblock_kept _ _ _ lyc Sc Uc W1 memC mdC ly' S' _ W' mem' md' _ kids (56 * cap)
      HJc HARU OK' PO'); [|exact KRB].
    intros z Hz. apply NFPk; [lia|].
    exact (proj1 (proj2 (proj2 (pio_rb_geo B lyc Sc W1 (unpoison Uc memC) mdC memC kids (56 * cap) z HAR KRB
      ltac:(lia))))).
  - apply (piv_rblock_kept _ _ _ lyc Sc Uc W1 memC mdC ly' S' _ W' mem' md' _ keys (8 * cap)
      HJc HARU OK' PO'); [|exact YRB].
    intros z Hz. apply NFPk; [intros Hc; unfold vk in Hc; piv_pd|].
    exact (proj1 (proj2 (proj2 (pio_rb_geo B lyc Sc W1 (unpoison Uc memC) mdC memC keys (8 * cap) z HAR YRB
      ltac:(lia))))). }
(* ---- the resume env ---- *)
set (xs := pib_xsK p' (text + len) (Z.of_nat k + 1) (map (YK11.getr regs) pi_saved_regs) kids keys
       (Z.of_nat (length dn)) cap a (Z.of_nat (length kk))).
destruct (piv_env_at B k S regs q ot v ms Hk HDEP regsC regs' xs pib_RL HRP HP) as (E9 & E19 & E32 & E2 & E3 & E4).
assert (XA : forall j, ew (Ereg regs' (fs_extraT ++ xs)) (xatom j) = nth j xs (Z_to_bv 64 0))
  by (intros j; apply fsw_ew_xatom).
destruct (pivv_xsK_nth p' (text + len) (Z.of_nat k + 1) (map (YK11.getr regs) pi_saved_regs) kids keys
  (Z.of_nat (length dn)) cap a (Z.of_nat (length kk)) (piv_xr_len regs))
  as (X0 & X1 & X2 & XR & X16 & X17 & X18 & X19 & X20 & X21).
assert (E9z : bv_unsigned (ew (Ereg regs' (fs_extraT ++ xs)) 9) = q) by (rewrite E9; apply wz; lia).
assert (E19z : bv_unsigned (ew (Ereg regs' (fs_extraT ++ xs)) 19) = v) by (rewrite E19; apply wz; lia).
assert (Y0 : ew (Ereg regs' (fs_extraT ++ xs)) (xatom 0) = Z_to_bv 64 p') by (rewrite XA; exact X0).
assert (Y1 : ew (Ereg regs' (fs_extraT ++ xs)) (xatom 1) = Z_to_bv 64 (text + len)) by (rewrite XA; exact X1).
assert (Y2 : ew (Ereg regs' (fs_extraT ++ xs)) (xatom 2) = Z_to_bv 64 (Z.of_nat k + 1)) by (rewrite XA; exact X2).
assert (Y16 : ew (Ereg regs' (fs_extraT ++ xs)) (xatom 16) = Z_to_bv 64 kids) by (rewrite XA; exact X16).
assert (Y17 : ew (Ereg regs' (fs_extraT ++ xs)) (xatom 17) = Z_to_bv 64 keys) by (rewrite XA; exact X17).
assert (Y18 : ew (Ereg regs' (fs_extraT ++ xs)) (xatom 18) = Z_to_bv 64 (Z.of_nat (length dn)))
  by (rewrite XA; exact X18).
assert (Y19 : ew (Ereg regs' (fs_extraT ++ xs)) (xatom 19) = Z_to_bv 64 cap) by (rewrite XA; exact X19).
assert (Y20 : ew (Ereg regs' (fs_extraT ++ xs)) (xatom 20) = Z_to_bv 64 a) by (rewrite XA; exact X20).
assert (Y21 : ew (Ereg regs' (fs_extraT ++ xs)) (xatom 21) = Z_to_bv 64 (Z.of_nat (length kk)))
  by (rewrite XA; exact X21).
(* ---- the frame, the regions, the atoms ---- *)
assert (HKEEP : forall z, spZ regs - 144 <= z < spZ regs ->
  mbyte tfibsegs (mrestrict (w_H W') mem') z = mbyte tfibsegs (mrestrict (w_H W1) memC) z)
  by (intros z Hz; exact (proj1 (HWK' z ltac:(rewrite Rsp; lia) ltac:(lia)))).
assert (HFL' : pib_frameL (mrestrict (w_H W') mem') (spZ regs) (map (YK11.getr regs) pi_saved_regs) q v)
  by exact (pivv_frameL_mb (mrestrict (w_H W1) memC) (mrestrict (w_H W') mem') (spZ regs)
       (map (YK11.getr regs) pi_saved_regs) q v HKEEP HFL).
assert (HCS : Forall (YP09.chunk_ok tfibsegs (Ereg regs' (fs_extraT ++ xs)) (mrestrict (w_H W') mem')
    (spZ regs - 144)) pib_csL).
{ apply (piv_csL_ok (Ereg regs' (fs_extraT ++ xs)) (mrestrict (w_H W') mem') (spZ regs)
    (map (YK11.getr regs) pi_saved_regs) q v (piv_xr_len regs));
    [| exact E9 | exact E19 | exact E32 | lia | lia | lia | exact HFL'].
  intros j Hj. rewrite XA. exact (XR j Hj). }
destruct (piv_text_rng B k S regs q ot text len tcap tb ms Hk HDEP ly' S' W' (unpoison (Uc ++ rd_heads Dx) mem') md'
  mem' p' (Z.of_nat k + 1) HAR' HTX' HIN') as (Rt1 & (Rt2a & Rt2b) & Rt3 & Rt4 & Rt5).
assert (HRS : Forall (region_ok tfibsegs (Ereg regs' (fs_extraT ++ xs)) (mrestrict (w_H W') mem')) pib_rs).
{ unfold pib_rs. constructor; [|constructor; [|constructor]].
  - exact (pis_q_ok (Ereg regs' (fs_extraT ++ xs)) (mrestrict (w_H W') mem') q text len p' (Z.of_nat k + 1) tb
      E9z Y0 Y1 Y2 HIN').
  - exact (piv_vR_ok (Ereg regs' (fs_extraT ++ xs)) (mrestrict (w_H W') mem') v 0 0 kids keys
      (Z.of_nat (length dn)) cap E19z Y16 Y17 Y18 Y19 ltac:(lia) ltac:(lia) VW' HHDR'). }
assert (HPD : pairwise_disjoint (Ereg regs' (fs_extraT ++ xs)) (fsT_ret_regions 144 pib_csL pib_rs))
  by exact (piv_disj (Ereg regs' (fs_extraT ++ xs)) (spZ regs - 144) q v E2 E9z E19z
       ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hvimg).
assert (HGF : atoms_ok (Ereg regs' (fs_extraT ++ xs)) pib_gfP).
{ apply (piv_gfP_ok (Ereg regs' (fs_extraT ++ xs)) q v p' (text + len) (Z.of_nat k + 1) kids keys
    (Z.of_nat (length dn)) cap a (Z.of_nat (length kk)) E9z E19z Y0 Y1 Y2 Y16 Y17 Y18 Y19 Y20 Y21);
    first [exact Hq8 | exact Hv8 | exact Kal | exact Yal | lia]. }
(* ---- the composed journal and the resume state ---- *)
assert (HFPS : fsw_fp_sub B ly S lyc Sc [] ([(v, v + 56)] ++ FS_PSTAT_FP) ([(vk, vk + 56)] ++ FS_PSTAT_FP)).
{ intros z Hz. apply inFP_app in Hz as [Hz|Hz].
  - right; left. exists (kids - HEAD), (56 * cap + HEAD). split; [exact KIN|]. split; [exact Ktmp|].
    rewrite piv_req by lia. apply inFP_cons in Hz as [Hz|Hz]; [lia | destruct (inFP_nil _ Hz)].
  - right; right; left. split; [apply inFP_app; right; exact Hz | exact (pim_pstat_img z Hz)]. }
destruct (pic_after_callT B (STK_parse_items (1 - k) + (ot - spZ regs)) ot ([(v, v + 56)] ++ FS_PSTAT_FP) []
  ly S U W1 mem md W lyc Sc Uc memC mdC (rd_ev T) (STK_parse_value (1 - k))
  ([(vk, vk + 56)] ++ FS_PSTAT_FP) (spZ regs) 144 regsC ly' S' (Uc ++ rd_heads Dx) W' regs' mem' md'
  (rd_ev (PjRoundTrip.ttrace x)) xs pib_csL pib_rs pib_gfP 0x851d0
  (proj1 HSS) (proj2 HSS) HJ HARU HJc HFPS OK' PO' HP Rsp ltac:(lia) HSTK0
  ltac:(rewrite Rsp; clear - Hsp16; Z.div_mod_to_equations; lia) ltac:(lia) ltac:(rewrite Rsp; lia)
  piv_wf HCS HRS HPD HGF) as (HJ2 & HARU2 & HST).
apply (K D Dx ly' S' W' regs' mem' md').
unfold pib_IH. cbv zeta.
split; [exact HIV|]. split; [exact HPm|]. split; [exact HJ2|]. split; [exact HJc|]. split; [exact HARU2|].
split; [exact HP|]. split; [exact A0|]. split; [exact HST|]. split; [exact HIN'|]. split; [exact HWK'|].
split; [exact HPERM'|]. split; [exact HRT|]. split; [exact HSUMx|]. split; [exact HLENx|]. split; [exact HPOk|].
split; [exact HTX'|]. split; [exact HG'|]. split; [exact HHDR'|]. split; [exact VBm|].
split; [exact BLK' | exact KBm].
Qed.

(* pib_RL at a call, restated over the call's own registers *)
Lemma piv_setr_RL : forall regsC regs' xs, pib_regsP B regs q v regsC pib_RL -> aregs_preserved regsC regs' ->
  Forall (fun r => fst r <> 0%bv /\ YK11.getr regs' (fst r) = sv_denot (Ereg regs' (fs_extraT ++ xs)) (snd r)) pib_RL.
Proof.
intros regsC regs' xs HR HP.
pose proof (piv_env_at B k S regs q ot v ms Hk HDEP regsC regs' xs pib_RL HR HP) as (E9 & E19 & E32 & _).
pose proof HR as (_ & R9 & R19 & _ & _ & RL).
pose proof piv_RL_ok as Hok. unfold piv_R_ok in Hok. rewrite forallb_forall in Hok.
rewrite Forall_forall in RL |- *.
intros [r e] Hin. pose proof (Hok _ Hin) as Hb. pose proof (RL _ Hin) as Hr. cbn [fst snd] in *.
apply andb_prop in Hb as [Hb Hat]. apply andb_prop in Hb as [Hb Hcs]. apply andb_prop in Hb as [H0 _].
split.
- intros ->. discriminate H0.
- rewrite (fsw_pres regsC regs' r HP).
  + rewrite Hr. apply pik_sv_denot_agree; [reflexivity|].
    intros n Hn. rewrite forallb_forall in Hat. pose proof (Hat n Hn) as Hn'.
    apply orb_prop in Hn' as [Hn'|Hn']; [apply orb_prop in Hn' as [Hn'|Hn']|]; apply Nat.eqb_eq in Hn'; subst n.
    * rewrite (ew_Ereg_nat regsC _ 9 9%bv eq_refl), R9. symmetry. exact E9.
    * rewrite (ew_Ereg_nat regsC _ 19 19%bv eq_refl), R19. symmetry. exact E19.
    * change 32%nat with (32 + 0)%nat. rewrite ew_Ereg_extra. cbn [nth fs_extraT app].
      rewrite <- E32. change 32%nat with (32 + 0)%nat. rewrite ew_Ereg_extra. reflexivity.
  + unfold acallee_saved. apply orb_prop in Hcs as [Hcs|Hcs]; [apply orb_prop in Hcs as [Hcs|Hcs]|].
    * apply Z.eqb_eq in Hcs. lia.
    * apply Z.eqb_eq in Hcs. lia.
    * apply andb_prop in Hcs as [Hc1 Hc2]. apply Z.leb_le in Hc1. apply Z.leb_le in Hc2. lia.
Qed.
(* a byte window at an atom: the key slot region of segment E *)
Lemma piv_kaR_ok : forall E m b, bv_unsigned (ew E (xatom 22)) = b -> 0 <= b -> b + 8 <= 2 ^ 64 ->
  (forall i, 0 <= i < 8 -> writable_at tfibsegs m (b + i)) -> region_ok tfibsegs E m pib_kaR.
Proof.
intros E m b Eb Hb0 Hb1 Hw. unfold region_ok, pib_kaR.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Eb.
split; [lia|]. split; [lia|]. split; [exact Hw | constructor].
Qed.
(* a live block's bytes are writable on the machine's memory (A's pic_block_writable) *)
Lemma piv_block_writable : forall ly1 S1 U1 (W1 : world tfibsegs) mem1 md1 b nb x,
  ARU tfibsegs B ly1 S1 U1 W1 mem1 md1 -> In (b, nb) (ablocks B ly1 S1) -> b <= x < b + req_size nb ->
  writable_at tfibsegs (mrestrict (w_H W1) mem1) x.
Proof.
intros ly1 S1 U1 W1 mem1 md1 b nb x HU Hin Hx. pose proof HU as (HAR & _ & _).
destruct (al_blocks tfibsegs B (AR_laws_ok tfibsegs B) ly1 S1 W1 (unpoison U1 mem1) md1 b nb HAR Hin)
  as (_ & _ & _ & _ & HP & _).
destruct (proj1 (HP x Hx)) as (Hh & c & Hc).
destruct (fsw_ablock_low B ly1 S1 W1 (unpoison U1 mem1) md1 b nb HAR Hin) as (A1 & A2 & _).
pose proof asan_consts as (C1 & _).
rewrite (fsw_unpoison_app B ly1 S1 U1 W1 mem1 md1 x HU ltac:(lia)
  (fsw_ablock_off_shadow B ly1 S1 W1 (unpoison U1 mem1) md1 b nb HAR Hin x Hx)) in Hc.
apply (apresent_writable tfibsegs). split; [exact Hh | exists c; exact Hc].
Qed.
Lemma piv_apart_of : forall a0 n0 b0 m0, 0 < n0 -> 0 < m0 -> (forall x, a0 <= x < a0 + n0 -> ~ (b0 <= x < b0 + m0)) ->
  a0 + n0 <= b0 \/ b0 + m0 <= a0.
Proof.
intros a0 n0 b0 m0 Hn Hm H. destruct (Z_lt_le_dec b0 (a0 + n0)) as [H1|H1]; [|left; exact H1].
destruct (Z_lt_le_dec a0 (b0 + m0)) as [H2|H2]; [|right; exact H2]. exfalso. apply (H (Z.max a0 b0)); lia.
Qed.

(* fs's statics are no read-only bytes, and its footprint is closed (A's pip_ro_not_pstat / pip_pstat_closed) *)
Lemma piv_ro_not_pstat : forall a0, in_roP tfibsegs FS_RLO FS_RHI a0 -> ~ inFP FS_PSTAT_FP a0.
Proof.
intros a0 Hro (r0 & Hr0 & Ha0). unfold FS_PSTAT_FP in Hr0. cbn [In] in Hr0.
assert (Hp : 0xa1000 <= fst r0) by (repeat (destruct Hr0 as [<-|Hr0]; [cbn; lia|]); destruct Hr0).
destruct Hro as [(sg & Hsg & Hw & Hr2) | Hr2].
- assert (HB : forallb (fun sg0 => seg_writable sg0 ||
    (Z.of_N (seg_base sg0) + Z.of_N (seg_size sg0) <=? 0xa1000)) tfibsegs = true) by (vm_compute; reflexivity).
  pose proof (proj1 (forallb_forall _ _) HB sg Hsg) as Hc. cbv beta in Hc. rewrite Hw in Hc. cbn [orb] in Hc.
  apply Z.leb_le in Hc. cbn [fst snd] in Ha0, Hp. lia.
- unfold FS_RLO, FS_RHI in Hr2. cbn [fst snd] in Ha0, Hp. lia.
Qed.
(* fs.asan's image bytes lie in [0x10000, FS_IMG_END) (A's pic_img_lo) *)
Lemma piv_img_lo : forall x0, in_img tfibsegs x0 -> 0x10000 <= x0 < FS_IMG_END.
Proof.
intros x0 Hx. pose proof (fs_segs_img x0 Hx) as Hu. split; [|lia].
destruct Hx as (sg & Hsg & Hr).
assert (HB : forallb (fun sg0 => 0x10000 <=? Z.of_N (seg_base sg0)) tfibsegs = true) by (vm_compute; reflexivity).
pose proof (proj1 (forallb_forall _ _) HB sg Hsg) as Hc. cbv beta in Hc. apply Z.leb_le in Hc. lia.
Qed.
Lemma piv_pstat_closed : ~ YI16.sink_open_fp FS_PSTAT_FP.
Proof. apply sink_closed_pos. unfold FS_PSTAT_FP. repeat constructor; cbn; lia. Qed.

(* the member loop's frame across a memory change that keeps [sp - 144, sp) *)
Lemma piv_frameL_mb : forall (M M' : word -> option byte) sp xr0 q0 v0,
  (forall a0, sp - 144 <= a0 < sp -> mbyte tfibsegs M' a0 = mbyte tfibsegs M a0) ->
  pib_frameL M sp xr0 q0 v0 -> pib_frameL M' sp xr0 q0 v0.
Proof.
intros M M' sp xr0 q0 v0 Hkeep (HF0 & F0 & F8 & F16 & F24 & F32).
assert (TR : forall off z, -144 <= off -> off + 8 <= 0 -> val_mem tfibsegs M (sp + off) 8 z ->
  val_mem tfibsegs M' (sp + off) 8 z).
{ intros off z H1 H2 Hv. apply (pim_val_mb M M' _ 8 _); [|exact Hv]. intros i0 Hi0. apply Hkeep. cbn in Hi0. lia. }
split.
- unfold pib_frame0 in *. rewrite Forall_forall in HF0 |- *. intros j Hj. apply in_seq in Hj.
  replace (sp - 8 - 8 * Z.of_nat j) with (sp + (- 8 - 8 * Z.of_nat j)) by lia.
  apply (TR (- 8 - 8 * Z.of_nat j)); [lia | lia|].
  replace (sp + (- 8 - 8 * Z.of_nat j)) with (sp - 8 - 8 * Z.of_nat j) by lia.
  apply HF0. apply in_seq. lia.
- split; [replace (sp - 144) with (sp + (-144)) by lia; apply (TR (-144)); [lia | lia |
    replace (sp + (-144)) with (sp - 144) by lia; exact F0]|].
  split; [replace (sp - 136) with (sp + (-136)) by lia; apply (TR (-136)); [lia | lia |
    replace (sp + (-136)) with (sp - 136) by lia; exact F8]|].
  split; [replace (sp - 128) with (sp + (-128)) by lia; apply (TR (-128)); [lia | lia |
    replace (sp + (-128)) with (sp - 128) by lia; exact F16]|].
  split; [replace (sp - 120) with (sp + (-120)) by lia; apply (TR (-120)); [lia | lia |
    replace (sp + (-120)) with (sp - 120) by lia; exact F24]|].
  replace (sp - 112) with (sp + (-112)) by lia; apply (TR (-112)); [lia | lia |
    replace (sp + (-112)) with (sp - 112) by lia; exact F32].
Qed.

(* ================= (EF) the resume after parse_string to the __asan_memset call ================= *)
Lemma piv_step_EF : forall dn kk x rm T lyc Sc Uc (W1 : world tfibsegs) memC mdC regsC chq pc kids keys cap Di Da
    peak1 a ly' S' (W' : world tfibsegs) regs' mem' md' (Qc : world tfibsegs -> config -> Prop),
  IE dn kk x rm T lyc Sc Uc W1 memC mdC regsC chq pc kids keys cap Di Da peak1 a ly' S' W' regs' mem' md' ->
  (forall T2 lyc2 Sc2 Uc2 (W2 : world tfibsegs) mem2 md2 regs2 chq2 pc2 Da2 peak2,
     IM dn kk x rm T2 lyc2 Sc2 Uc2 W2 mem2 md2 regs2 chq2 pc2 kids keys cap Di Da2 peak2 a ->
     SRr tfibsegs W2 (YG0d.cfg_at tfibsegs PC_memset regs2 mem2 md2) Qc) ->
  SRr tfibsegs W' (mkCfg (mkst regs' (Z_to_bv 64 0x85048) mem' (seg_rom tfibsegs)) md') Qc.
Proof.
intros dn kk x rm T lyc Sc Uc W1 memC mdC regsC chq pc kids keys cap Di Da peak1 a ly' S' W' regs' mem' md' Qc HIE K.
unfold pib_IE in HIE. cbv zeta in HIE.
destruct HIE as (HIP & HJ2 & HJps & HARU' & HP' & R10' & HST & Ha16 & HAB' & HRB' & HCB' & HIN' & HWK' & HTX' & HG' &
  HHDR' & HV' & HBK' & HKY').
unfold pib_IP in HIP. cbv zeta in HIP.
destruct HIP as (Hms & Htr & Hi & Hc54 & HJC & R1 & R10 & HRP & HFL & HSTK & HRST & HBL & HOB).
pose proof HJC as (HJ & HARU & HRO & HHD).
pose proof HRP as (Rsp & R9 & R19 & R3 & R4 & RL).
pose proof HSTK as (HCH & HCHF & Htop & HIN & HWK).
pose proof HBL as (HTX1 & HPO1 & HBK1 & HPERM1 & HUc & HDa & HSUM & HLEN & HG1 & Hpk).
pose proof HOB as (HHDR1 & HOPEN1).
pose proof HARU as (HAR & _ & _). pose proof HARU' as (HAR' & HUOK' & HUPO').
pose proof asan_consts as (C1 & _ & C3 & _).
pose proof (AR_laws_ok tfibsegs B) as LAWS.
assert (HEADv : HEAD = 16) by reflexivity.
assert (Hxl : length xr = 13%nat) by exact (piv_xr_len regs).
(* ---- the entry's numbers ---- *)
destruct (piv_sp0 B k ly S U W regs mem md ot ms ch Hk HPRE HDEP) as (Hsp16 & HspC & Hsp47).
pose proof (piv_stk144 k S regs ot ms Hk HDEP) as Hstk144.
destruct (piv_v_rng B k ly S U W regs mem md v ch HPRE HPO0) as (Hv1 & Hv2).
destruct (piv_q_stack B k ly S U W regs mem md q ot text len p tb ms ch Hk HPRE HWIN HQ16 HIN0 HDEP)
  as (Hqlo & Hqhi & Hq8 & Hqc & Hq47).
pose proof HWIN as (Hsq & Hq24 & Hot16 & Hotly & Hpot).
pose proof HPRE as ((HAP0 & _ & _) & _). pose proof HAP0 as (_ & _ & _ & _ & _ & Hstk0 & _).
pose proof Hstk0 as (_ & _ & Hceil0 & Hslo0 & Hshi0 & H470 & _ & Htop0 & Htop20).
assert (HVTXh : piv_hide (v + 56 <= text - HEAD \/ text + tcap <= v)) by exact HVTX.
assert (HVSPh : piv_hide (v + 56 <= spZ regs - STK_parse_items (1 - k) \/ ot <= v)) by exact HVSP.
clear HVTX HVSP.
destruct (piv_text_rng B k S regs q ot text len tcap tb ms Hk HDEP lyc Sc W1 (unpoison Uc memC) mdC memC pc
  (Z.of_nat k + 1) HAR HTX1 HIN) as (Htx1 & (Hpc1 & Hpc2) & Htx3 & Htx4 & Hac47).
assert (Hcap0 : 0 < cap) by lia.
assert (Hn0 : 0 <= Z.of_nat (length dn)) by lia.
assert (Hncap : Z.of_nat (length dn) < cap) by lia.
(* ---- the kids / keys blocks of v at the call ---- *)
assert (ES : parse_items_shape.pis_slots true kids keys cap = [(kids, 56 * cap); (keys, 8 * cap)]).
{ unfold parse_items_shape.pis_slots, ReaderRes.kids_blk, ReaderRes.keys_blk.
  rewrite (proj2 (Z.eqb_neq cap 0)) by lia. reflexivity. }
assert (HinKL : In (kids, 56 * cap) (parse_items_shape.pis_slots true kids keys cap ++ Di))
  by (apply in_or_app; left; rewrite ES; left; reflexivity).
assert (HinYL : In (keys, 8 * cap) (parse_items_shape.pis_slots true kids keys cap ++ Di))
  by (apply in_or_app; left; rewrite ES; right; left; reflexivity).
pose proof (HBK1 _ _ HinKL) as KRB1. pose proof (HBK1 _ _ HinYL) as YRB1.
pose proof KRB1 as (KIN1 & Kal & _ & _). pose proof YRB1 as (YIN1 & Yal & _ & _).
destruct (fsw_rblock_low B lyc Sc W1 (unpoison Uc memC) mdC memC kids (56 * cap) HAR KRB1) as (HKlo & HKhi).
destruct (fsw_rblock_low B lyc Sc W1 (unpoison Uc memC) mdC memC keys (8 * cap) HAR YRB1) as (HYlo & HYhi).
pose proof (fsw_ablock_off_img B lyc Sc W1 (unpoison Uc memC) mdC _ _ HAR YIN1) as HYimg.
pose proof (fsw_ablock_off_img B lyc Sc W1 (unpoison Uc memC) mdC _ _ HAR KIN1) as HKimg.
rewrite (piv_req (8 * cap)) in HYimg by lia. rewrite (piv_req (56 * cap)) in HKimg by lia.
assert (HYimgh : piv_hide (keys + 8 * cap <= 65536 \/ 6279168 <= keys - 16))
  by (unfold piv_hide; destruct HYimg as [Hz|Hz]; [left | right]; unfold FS_IMG_END, HEAD in *; lia).
assert (HKimgh : piv_hide (kids + 56 * cap <= 65536 \/ 6279168 <= kids - 16))
  by (unfold piv_hide; destruct HKimg as [Hz|Hz]; [left | right]; unfold FS_IMG_END, HEAD in *; lia).
clear HYimg HKimg.
pose proof HOPEN1 as (_ & HAPL & _).
assert (HYV : keys + 8 * Z.of_nat (length dn) + 8 <= v \/ v + 56 <= keys + 8 * Z.of_nat (length dn)).
{ apply piv_apart_of; [lia | lia |]. intros z Hz Hzv.
  apply (HAPL (keys, 8 * cap) z); [exact HinYL | unfold PjStruct.pj_holds; cbn [fst snd]; lia | exact Hzv]. }
assert (HKV : kids + 56 * Z.of_nat (length dn) + 56 <= v \/ v + 56 <= kids + 56 * Z.of_nat (length dn)).
{ apply piv_apart_of; [lia | lia |]. intros z Hz Hzv.
  apply (HAPL (kids, 56 * cap) z); [exact HinKL | unfold PjStruct.pj_holds; cbn [fst snd]; lia | exact Hzv]. }
assert (HYVh : piv_hide (keys + 8 * Z.of_nat (length dn) + 8 <= v \/ v + 56 <= keys + 8 * Z.of_nat (length dn)))
  by exact HYV.
assert (HKVh : piv_hide (kids + 56 * Z.of_nat (length dn) + 56 <= v \/ v + 56 <= kids + 56 * Z.of_nat (length dn)))
  by exact HKV.
clear HYV HKV.
(* the keys / kids blocks after parse_string, and the key block *)
assert (EDb : ReaderRes.kids_blk kids cap ++ ReaderRes.keys_blk 6 keys cap = [(kids, 56 * cap); (keys, 8 * cap)])
  by (unfold ReaderRes.kids_blk, ReaderRes.keys_blk; rewrite (proj2 (Z.eqb_neq cap 0)) by lia; reflexivity).
pose proof HBK' as HBK''. rewrite EDb in HBK''.
pose proof (HBK'' kids (56 * cap) (or_introl eq_refl)) as KRB'.
pose proof (HBK'' keys (8 * cap) (or_intror (or_introl eq_refl))) as YRB'.
pose proof KRB' as (KIN' & _ & _ & _). pose proof YRB' as (YIN' & _ & _ & _).
assert (HnotY : ~ In (keys - HEAD, 8 * cap + HEAD) (ablocks B ly S)).
{ apply (piv_not_entry B ly S lyc Sc W1 (unpoison Uc memC) mdC _ HAR HPERM1).
  unfold rd_hblocks. apply (in_map (fun b => (fst b - HEAD, snd b + HEAD)) _ _ HinYL). }
(* ---- the text at in->p: the key, then `:` ---- *)
destruct (piv_mem_facts k S regs ot ms Hk HDV HDS HWF HDEP dn kk x rm Hms) as (Hplain & Hsoo & Hstr & Hwf & Hdep).
rewrite (pim_spieces_plain kk Hplain), (pim_wsep pr) in HRST.
set (wsp := if pr then [32] else []) in HRST.
set (R0 := concat (WriterValue.wvpieces x pr (dd + 1)) ++ concat (pi_mgo pr dd (Datatypes.S (length dn)) rm) ++
  pib_wsb pr dd ++ [125] ++ rest) in HRST.
pose proof (PjIn.pj_in_ok_bounds tfibsegs _ _ _ _ _ _ _ HIN)
  as (Hq0b & Hq64b & Ht0b & (Hpc1b & Hpc2b) & Hteb & Hqapb & Htblen & Hq8b & Hdb).
assert (HRlen : forall p', text <= p' -> Z.of_nat (length (ReaderRes.rest_at tb text p')) = Z.max 0 (text + len - p')).
{ intros p' Hp'. unfold ReaderRes.rest_at, ReaderRes.zb. rewrite length_map, length_skipn. lia. }
assert (HR1 : ReaderRes.rest_at tb text pc = 34 :: kk ++ 34 :: 58 :: wsp ++ R0)
  by (rewrite HRST; cbn [app]; rewrite <- app_assoc; reflexivity).
destruct (pim_key_run tb text len pc kk (58 :: wsp ++ R0) Hpc1 ltac:(rewrite HRlen by lia; lia) HR1 Hplain)
  as (Hrun & Hrunat & Hq34 & Hpclt).
assert (HRc : ReaderRes.rest_at tb text (pc + Z.of_nat (length kk) + 2) = 58 :: wsp ++ R0).
{ replace (pc + Z.of_nat (length kk) + 2) with (pc + Z.of_nat (length (34 :: kk ++ [34])))
    by (cbn [length]; rewrite length_app; cbn [length]; lia).
  apply pim_rest_skip; [lia|]. rewrite HR1. cbn [app]. rewrite <- app_assoc. reflexivity. }
assert (HRd : ReaderRes.rest_at tb text (pc + Z.of_nat (length kk) + 3) = wsp ++ R0).
{ replace (pc + Z.of_nat (length kk) + 3) with (pc + Z.of_nat (length kk) + 2 + Z.of_nat (length [58]))
    by (cbn [length]; lia).
  apply pim_rest_skip; [lia|]. rewrite HRc. reflexivity. }
assert (Hcolon : pc + Z.of_nat (length kk) + 2 < text + len).
{ pose proof (HRlen (pc + Z.of_nat (length kk) + 2) ltac:(lia)) as HL. rewrite HRc in HL. cbn [length] in HL. lia. }
(* ---- the resume env ---- *)
set (xs := pib_xsK (pc + Z.of_nat (length kk) + 2) (text + len) (dd + 1) xr kids keys (Z.of_nat (length dn)) cap a
  (Z.of_nat (length kk))) in *.
set (E := Ereg regs' (fs_extraT ++ xs)) in *.
set (MS := restrict (w_H W') (mkst regs' (Z_to_bv 64 0x85048) mem' (seg_rom tfibsegs))) in *.
destruct (piv_xsK_nth (pc + Z.of_nat (length kk) + 2) (text + len) (dd + 1) xr kids keys (Z.of_nat (length dn)) cap a
  (Z.of_nat (length kk)) Hxl) as (X0 & X1 & X2 & XR & X16 & X17 & X18 & X19 & X20 & X21 & X22 & X23 & Hxs24).
fold xs in X0, X1, X2, XR, X16, X17, X18, X19, X20, X21, X22, X23, Hxs24.
assert (EXn : forall j, ew E (xatom j) = nth j xs (Z_to_bv 64 0)) by (intros j; unfold E; apply fsw_ew_xatom).
assert (Ex0 : ew E (xatom 0) = Z_to_bv 64 (pc + Z.of_nat (length kk) + 2)) by (rewrite EXn; exact X0).
assert (Ex1 : ew E (xatom 1) = Z_to_bv 64 (text + len)) by (rewrite EXn; exact X1).
assert (Ex2 : ew E (xatom 2) = Z_to_bv 64 (dd + 1)) by (rewrite EXn; exact X2).
assert (Ex16 : ew E (xatom 16) = Z_to_bv 64 kids) by (rewrite EXn; exact X16).
assert (Ex17 : ew E (xatom 17) = Z_to_bv 64 keys) by (rewrite EXn; exact X17).
assert (Ex18 : ew E (xatom 18) = Z_to_bv 64 (Z.of_nat (length dn))) by (rewrite EXn; exact X18).
assert (Ex19 : ew E (xatom 19) = Z_to_bv 64 cap) by (rewrite EXn; exact X19).
assert (Ex20 : ew E (xatom 20) = Z_to_bv 64 a) by (rewrite EXn; exact X20).
assert (Ex22 : ew E (xatom 22) = Z_to_bv 64 (keys + 8 * Z.of_nat (length dn))) by (rewrite EXn; exact X22).
assert (Ex23 : ew E (xatom 23) = Z_to_bv 64 (kids + 56 * Z.of_nat (length dn))) by (rewrite EXn; exact X23).
destruct (piv_env_at B k S regs q ot v ms Hk HDEP regsC regs' xs pib_RL HRP HP') as (E9 & E19 & E32 & E2u & E3 & E4).
fold E in E9, E19, E32, E2u, E3, E4.
assert (E9u : bv_unsigned (ew E 9) = q) by (rewrite E9; apply wz; lia).
assert (E19u : bv_unsigned (ew E 19) = v) by (rewrite E19; apply wz; lia).
assert (Ex22u : bv_unsigned (ew E (xatom 22)) = keys + 8 * Z.of_nat (length dn)) by (rewrite Ex22; apply wz; lia).
assert (Ex0u : bv_unsigned (ew E (xatom 0)) = pc + Z.of_nat (length kk) + 2) by (rewrite Ex0; apply wz; lia).
assert (UBx : YP0e.U E fs_Bx = SHADOW_OFF) by (unfold fs_Bx; apply U_atom; [exact E32 | unfold SHADOW_OFF; lia]).
(* ---- the heads, v and the layout after parse_string ---- *)
assert (HH' : FSupoisonU.fs_heads B ly' S' (Uc ++ [(a - HEAD, HEAD)])).
{ intros r0 Hr0. apply in_app_or in Hr0 as [Hr0 | [<- | []]].
  - destruct (HHD r0 Hr0) as (H16 & m0 & Hm0 & Hrq). split; [exact H16|]. exists m0.
    split; [rewrite HAB'; apply in_or_app; left; exact Hm0 | exact Hrq].
  - split; [reflexivity|]. exists (Z.of_nat (length kk) + 1 + HEAD).
    split; [rewrite HAB'; apply in_or_app; right; left; reflexivity|].
    rewrite piv_req by lia. unfold HEAD. lia. }
assert (HPO' : pobj tfibsegs B ly' S' W' mem' v).
{ apply (pobj_kept_call B _ _ FS_PSTAT_FP lyc Sc Uc W1 memC mdC ly' S' _ W' mem' md' EV_fuzz_malloc v HJps HARU HUOK'
    HUPO'); [| exact pio_pstat_off_shadow | exact HH' | exact HPO1].
  intros z Hz. apply pio_pstat_off.
  pose proof (fsw_pobj_off_img B lyc Sc W1 (unpoison Uc memC) mdC memC v HAR HPO1) as Hvi. unfold FS_IMG_END in *. lia. }
pose proof HJ2 as (_ & Hly2 & _).
pose proof Hly2 as (_ & _ & _ & _ & _ & _ & _ & _ & Htop2 & Hslo2 & Hshi2 & _).
(* ---- the start state of segment E ---- *)
assert (HS1 : st_ok tfibsegs E (pik_setm (fss_retT 0x85048 144 pib_csL pib_rs pib_gfP)
  (pib_rgs pib_csL pib_RO pib_RO pib_RO)) MS)
  by exact (pik_st_ok_setm E _ _ _ HST piv_submem_E piv_wf_E).
assert (Ha0 : YK11.getr regs' 10 = sv_denot E (SOff (xatom 20) 0)) by (rewrite fsw_SOff0, Ex20; exact R10').
assert (HS2 : st_ok tfibsegs E (pik_setr (pik_setm (fss_retT 0x85048 144 pib_csL pib_rs pib_gfP)
  (pib_rgs pib_csL pib_RO pib_RO pib_RO)) ((10%bv, SOff (xatom 20) 0) :: pib_RL)) MS).
{ apply pik_st_ok_setr; [exact HS1|]. cbn [ms_regs mkst restrict].
  exact (piv_setr_ok B k S regs q ot v ms Hk HDEP regsC regs' xs pib_RL (SOff (xatom 20) 0) HRP HP' piv_RL_ok Ha0). }
assert (RKA : region_ok tfibsegs E (mrestrict (w_H W') mem') pib_kaR).
{ apply (piv_kaR_ok E _ (keys + 8 * Z.of_nat (length dn)) Ex22u ltac:(lia) ltac:(lia)).
  intros i0 Hi0'.
  apply (piv_block_writable ly' S' (Uc ++ [(a - HEAD, HEAD)]) W' mem' md' (keys - HEAD) (8 * cap + HEAD));
    [exact HARU' | exact YIN' | rewrite piv_req by lia; unfold HEAD in *; lia]. }
assert (DJ1 : all_disjoint E pib_kaR (pib_rgs pib_csL pib_RO pib_RO pib_RO)).
{ apply all_disjoint_of_extents.
  unfold pib_rgs, pib_kaR, pib_RO, fs_got_region, fs_bcell_region, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val fst snd]. rewrite Ex22u, E2u, E9u, E19u.
  unfold tfib_D_GOT_asan_shadow_memory_dynamic_address, tfib_D_asan_shadow_memory_dynamic_address, FS_IMG_END,
    HEAD in *.
  cbn [zall_disjoint]. unfold zdisj. cbn [fst snd].
  repeat match goal with |- _ /\ _ => split end; try exact I; piv_pd. }
assert (HS3 : st_ok tfibsegs E (pik_addr (pik_setr (pik_setm (fss_retT 0x85048 144 pib_csL pib_rs pib_gfP)
  (pib_rgs pib_csL pib_RO pib_RO pib_RO)) ((10%bv, SOff (xatom 20) 0) :: pib_RL)) [pib_kaR]) MS).
{ unfold pik_addr. cbn [app].
  apply st_ok_add_region'; [exact HS2 | vm_compute; reflexivity | | exact DJ1].
  unfold MS. rewrite restrict_mem. cbn [ms_mem mkst]. exact RKA. }
assert (HAT : atoms_ok E pib_gf_ka).
{ unfold pib_gf_ka. cbn [atoms_ok]. split; [|exact I]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite Ex22u. change (2 ^ 3) with 8. split; [lia|]. split; [|lia].
  clear - Yal Hn0. Z.div_mod_to_equations. lia. }
assert (HCD : conds_ok E [pib_c_n60; pib_geu (xatom 22) (xatom 17)]).
{ cbn [conds_ok]. split; [exact (piv_c_n60_ok E (Z.of_nat (length dn)) Ex18 ltac:(lia))|].
  split; [|exact I].
  exact (piv_geu_ok E (xatom 22) (xatom 17) (keys + 8 * Z.of_nat (length dn)) keys Ex22 Ex17 ltac:(lia) ltac:(lia)
    ltac:(lia)). }
assert (HAL : alias_ok E [pib_al_ka]).
{ destruct (pik_alias_ok_lin E (xatom 17) (xatom 18) (xatom 22) keys (Z.of_nat (length dn)) Ex17 Ex18 ltac:(lia)
    ltac:(lia)) as (AL1 & _).
  exact (AL1 ltac:(lia) Ex22). }
assert (HSE : st_ok tfibsegs E pib_ss_E MS) by (apply pik_st_ok_addf; [exact HS3 | exact HAT | exact HCD | exact HAL]).
(* ---- the shadow entries and the write permissions of the run ---- *)
assert (SHOK : sh_ok tfibsegs fs_Bx pib_SHe E (mrestrict (w_H W') mem')).
{ unfold sh_ok, pib_SHe, pib_SHm. repeat apply Forall_cons; try apply Forall_nil.
  - apply (piv_sh_blk B k S regs ot ms Hk HDEP ly' S' (Uc ++ [(a - HEAD, HEAD)]) W' mem' md' E (xatom 22)
      (keys - HEAD) (8 * cap + HEAD) (keys + 8 * Z.of_nat (length dn)) 0 8 HARU' HH' YIN');
      [unfold HEAD in *; lia | lia | unfold HEAD in *; lia | exact UBx |].
    apply U_atom; [exact Ex22 | lia].
  - apply (piv_sh_q B k ly S U W regs mem md q ot text len p tb ms ch Hk HPRE HWIN HQ16 HIN0 HDEP ly' S'
      (Uc ++ [(a - HEAD, HEAD)]) W' mem' md' E 9 HARU' Hslo2 Hshi2 UBx).
    apply U_atom; [exact E9 | lia].
  - apply (piv_sh_v B k S regs ot v ms Hk HDEP ly' S' (Uc ++ [(a - HEAD, HEAD)]) W' mem' md' E 19 HARU' HPO' UBx).
    apply U_atom; [exact E19 | lia]. }
assert (AWR : awr_ok tfibsegs B E (ss_mem pib_ss_E) STKt ot FP (ablocks B ly S) (ablocks B ly' S') ly' []
  (frames S)).
{ assert (Hm : ss_mem pib_ss_E = [pib_kaR; YP09.mkRegion (Some 2%nat) 0 144 0 0 pib_csL; fs_got_region;
    fs_bcell_region 32; YP09.mkRegion (Some 9%nat) 0 24 0 0 (YP09.r_chunks pi_qR);
    YP09.mkRegion (Some 19%nat) 0 56 0 0 pib_vch]) by reflexivity.
  rewrite Hm.
  eapply awr_ok_cons_gen with (k := xatom 22) (b := keys + 8 * Z.of_nat (length dn));
    [reflexivity | exact Ex22u | |].
  { intros a0 Ha0'. cbn [pib_kaR YP09.r_wlo YP09.r_whi] in Ha0'. left. right. right. left.
    exists (keys - HEAD), (8 * cap + HEAD). split; [exact YIN'|]. split; [exact HnotY|].
    rewrite piv_req by lia. unfold HEAD in *. lia. }
  apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn [fs_got_region YP09.r_wlo YP09.r_whi]; lia|].
  apply awr_ok_cons_ro; [cbn [fs_bcell_region YP09.r_wlo YP09.r_whi]; lia|].
  apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
(* ---- the run of segment E ---- *)
pose proof HTX as HTX0. pose proof HTX0 as (_ & HRBT0 & _). pose proof HRBT0 as (HinT0 & _).
destruct piv_fin_E as (HpcE & HobE & HresE & HjE & HregsE & HmE0 & HmE1 & HmE4 & HKE).
eapply (fsw_run_tok_AJU B pitems_tbl pitems_tbl_ok W' FUEL E (run_K 0 fs_Bx pib_SHe pib_ss_E) fs_Bx fs_Bspan pib_SHe
  pib_ss_E pib_st_E (TS_stopped SR_fetch) (mkst regs' (Z_to_bv 64 0x85048) mem' (seg_rom tfibsegs))
  STKt ot FP ly S W (unpoison U mem) md [] ly' S' (Uc ++ [(a - HEAD, HEAD)]) md' (rd_ev T + EV_fuzz_malloc) Qc
  HSE SHOK pib_static_E pib_run_E I HARU' HJ2 ltac:(rewrite HobE; constructor) AWR).
intros ws ms2 mat2 Hlen2 HS2r SHOK2 HJ2b HARU2 HFm2 HFr2 HGr2.
rewrite HjE in Hlen2. destruct ws as [|w0 ws]; [clear Hlen2 | discriminate Hlen2].
cbn [extK] in HS2r, SHOK2.
(* ---- what the run kept, and the store keys[n] := a ---- *)
assert (HRAW : forall z, 0 <= z < 2 ^ 64 ->
  ~ (keys + 8 * Z.of_nat (length dn) <= z < keys + 8 * Z.of_nat (length dn) + 8) ->
  mrestrict (w_H W') (ms_mem ms2) (Z_to_bv 64 z) = mrestrict (w_H W') mem' (Z_to_bv 64 z)).
{ intros z Hz Hnz. apply HFr2. rewrite wz by lia. intros Hw. apply piv_wr_E in Hw. rewrite Ex22u in Hw. lia. }
destruct (fsw_rblock_low B ly' S' W' (unpoison (Uc ++ [(a - HEAD, HEAD)]) mem') md' mem' a
  (Z.of_nat (length kk) + 1) HAR' HRB') as (Halo & Hahi).
assert (RKA2 : region_ok tfibsegs E (mrestrict (w_H W') (ms_mem ms2))
  (YP09.mkRegion (Some (xatom 22)) 0 8 0 8 [YP09.mkChunk 0 (CVal 8 (SOff (xatom 20) 0))]))
  by exact (fsw_region_nth E _ _ 0 _ HS2r HmE0).
pose proof (fsw_field E _ (xatom 22) _ _ 0 8 0 8 0 8 (SOff (xatom 20) 0) a RKA2 Ex22u ltac:(left; reflexivity)
  ltac:(rewrite fsw_SOff0; exact Ex20) ltac:(cbn; lia) ltac:(cbn; lia)) as HVAL.
rewrite Z.add_0_r in HVAL.
pose proof RKA2 as (_ & _ & RKW & _).
cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in RKW. rewrite Ex22u in RKW.
assert (HCB2 : PjStruct.pj_cbytes tfibsegs (mrestrict (w_H W') mem') a kk) by (rewrite <- Hrunat; exact HCB').
(* ---- the object after the store (FSW_parse_items_obj.pio_key) ---- *)
destruct (pio_key B ly S U lyc Sc Uc W1 memC mdC ly' S' W' mem' md' (ms_mem ms2)
  (STK_parse_string + (ot - spZ regsC)) ot v text len tcap (length dn) dn kids keys cap Di Da T a kk
  eq_refl ltac:(lia) Hc54 HARU HHD HHEADS HTX1 HinT0 HPO1 HBK1 HPERM1 HUc HDa HSUM HLEN HHDR1 HOPEN1 HJps HARU'
  Ha16 HAB' HRB' HCB2 HTX' HHDR' HV' HBK' HKY' HVAL
  ltac:(intros z Hz Hnz; apply HRAW; [lia | lia])
  ltac:(intros z Hz; replace z with (keys + 8 * Z.of_nat (length dn) + (z - (keys + 8 * Z.of_nat (length dn))))
        by lia; apply RKW; lia))
  as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12 & K13 & K14).
(* ---- the stop of segment E: the registers and the memory ---- *)
pose proof (piv_regs_of_stop E _ ms2 (w_H W') _ HS2r HregsE) as RG. rewrite Forall_forall in RG.
assert (RGf : forall r0 e0, In (r0, e0) piv_regs_E -> YK11.getr (ms_regs ms2) r0 = sv_denot E e0)
  by (intros r0 e0 Hin; exact (RG (r0, e0) Hin)).
pose proof (RGf 1%bv (SLit 0x850bc) ltac:(unfold piv_regs_E; cbn [In app]; tauto)) as G1.
pose proof (RGf 2%bv (SOff 2 0) ltac:(unfold piv_regs_E; cbn [In app]; tauto)) as G2.
pose proof (RGf 3%bv (SOff 3 0) ltac:(unfold piv_regs_E; cbn [In app]; tauto)) as G3.
pose proof (RGf 4%bv (SOff 4 0) ltac:(unfold piv_regs_E; cbn [In app]; tauto)) as G4.
pose proof (RGf 8%bv (SOff 9 16) ltac:(unfold piv_regs_E; cbn [In app]; tauto)) as G8.
pose proof (RGf 9%bv (SOff 9 0) ltac:(unfold piv_regs_E; cbn [In app]; tauto)) as G9.
pose proof (RGf 10%bv (SOff 9 0) ltac:(unfold piv_regs_E; cbn [In app]; tauto)) as G10.
pose proof (RGf 19%bv (SOff 19 0) ltac:(unfold piv_regs_E; cbn [In app]; tauto)) as G19.
rewrite fsw_SOff0 in G2, G3, G4, G9, G10, G19.
(* ---- the facts skip_ws reads, at the stop's memory ---- *)
pose proof HTX1 as (_ & HRBT1 & _). pose proof HRBT1 as (HinT1 & _ & Htc0 & _).
assert (HTY : text - HEAD + (tcap + HEAD) <= keys - HEAD \/ keys - HEAD + (8 * cap + HEAD) <= text - HEAD).
{ assert (Hne : (text - HEAD, tcap + HEAD) <> (keys - HEAD, 8 * cap + HEAD))
    by (intros Heq; apply HnotY; rewrite <- Heq; exact HinT0).
  pose proof (sep_blocks tfibsegs B LAWS lyc Sc W1 (unpoison Uc memC) mdC _ _ _ _ HAR HinT1 YIN1 Hne) as Hz.
  unfold zdisjoint in Hz. cbn [fst snd] in Hz. rewrite !piv_req in Hz by lia. exact Hz. }
assert (HTYh : piv_hide (text + tcap <= keys - 16 \/ keys + 8 * cap <= text - 16))
  by (unfold piv_hide; destruct HTY as [Hz|Hz]; [left | right]; unfold HEAD in *; lia).
clear HTY.
assert (HIN2 : PjIn.pj_in_ok tfibsegs (mrestrict (w_H W') (ms_mem ms2)) q text len
  (pc + Z.of_nat (length kk) + 2) (dd + 1) tb).
{ apply (pim_eqon_in (mrestrict (w_H W') mem') _ q text len (pc + Z.of_nat (length kk) + 2) (dd + 1) tb);
    [intros z Hz; apply HRAW; [lia | lia] | intros z Hz; apply HRAW; [lia | piv_pd] | exact HIN']. }
assert (HTX2 : rd_text tfibsegs B ly' S' W' (ms_mem ms2) text len tcap).
{ pose proof HTX' as (T1 & T2 & T3). split; [exact T1|]. split; [|exact T3].
  apply (pio_rblock_keep B ly' S' W' mem' (ms_mem ms2) text tcap T2).
  intros z Hz. apply HRAW; [lia | piv_pd]. }
assert (HG2 : fs_glob tfibsegs W' (ms_mem ms2) (live + PjGrammar.held T + Z.of_nat (length kk) + 1)
  (Z.max peak1 (live + PjGrammar.held T + Z.of_nat (length kk) + 1))
  (cnt + Z.of_nat (length T) + 1) fail).
{ apply (pim_glob_eqon W' W' mem' (ms_mem ms2)); [|exact HG'].
  intros z Hz. destruct (piv_img_lo z (pim_pstat_img z Hz)) as (Hz1 & Hz2).
  unfold FS_IMG_END in Hz2. apply HRAW; [lia | piv_pd]. }
assert (HRO' : arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W') mem'))
  by exact (arodata_kept B _ _ FS_PSTAT_FP lyc Sc Uc W1 memC mdC ly' S' _ W' mem' md' EV_fuzz_malloc HJps HARU HUOK'
     HUPO' piv_pstat_closed piv_ro_not_pstat HRO).
assert (HRO2 : arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W') (ms_mem ms2))).
{ intros z Hz Ho He. rewrite <- (HRO' z Hz Ho He). apply pio_aview_raw.
  destruct (piv_img_lo z (fsw_roP_img z Hz)) as (Hz1 & Hz2). unfold FS_IMG_END in Hz2.
  apply HRAW; [lia | piv_pd]. }
(* ---- the call of skip_ws #3 ---- *)
rewrite (st_ok_restrict_mkst tfibsegs (w_H W') E _ ms2 HS2r HresE), HpcE.
apply (pic_call_sw SK B HSW STKt ot FP ly S W (unpoison U mem) md [] ly' S' (Uc ++ [(a - HEAD, HEAD)]) W'
  (ms_mem ms2) (with_vm_backing (m_vm_lazy md') mat2 md') (rd_ev T + EV_fuzz_malloc) (ms_regs ms2) q text len
  (pc + Z.of_nat (length kk) + 2) (dd + 1) tb tcap [] (58 :: wsp ++ R0)
  (live + PjGrammar.held T + Z.of_nat (length kk) + 1) (Z.max peak1 (live + PjGrammar.held T + Z.of_nat (length kk) + 1))
  (cnt + Z.of_nat (length T) + 1) fail Qc HJ2b HARU2 HRO2 HH').
- rewrite G1. unfold YK0s.ret_ok. vm_compute. reflexivity.
- unfold raZ. rewrite G1. cbn [sv_denot]. rewrite unsigned_lit_small by lia. lia.
- rewrite G3. exact E3.
- rewrite G4. exact E4.
- rewrite G10. rewrite E9. reflexivity.
- rewrite G8. rewrite (piv_den_off E 9 q 16 E9 ltac:(lia) ltac:(lia) ltac:(lia)). reflexivity.
- unfold spZ. rewrite G2, E2u. rewrite Zminus_mod, Hsp16. reflexivity.
- unfold spZ. rewrite G2, E2u. unfold STKt.
  assert (HSW144 : STK_skip_ws + 144 <= STK_parse_items (1 - k))
    by (unfold STK_parse_items, STK_parse_items_of, zmaxl, FRAME_parse_items; cbn [fold_right]; lia).
  lia.
- unfold spZ. rewrite G2, E2u. lia.
- lia.
- exact HIN2.
- exact HTX2.
- cbn [app]. exact HRc.
- constructor.
- intros c0 r0 Hc0. injection Hc0 as <- _. vm_compute. reflexivity.
- exact HG2.
- intros ly3 S3 W3 regs3 mem3 md3 HJsw OKsw POsw HPsw QIN QWK QAB QTX QGL.
  rewrite G1.
  change (sv_denot E (SLit 0x850bc)) with (Z_to_bv 64 0x850bc).
  (* ---- the callee-saved registers and the frame at the resume ---- *)
  assert (HRLcs : forall r0 e0, In (r0, e0) pib_RL -> acallee_saved (bv_unsigned r0)).
  { intros r0 e0 Hin. unfold pib_RL in Hin. cbn [In] in Hin.
    repeat (destruct Hin as [Eq|Hin]; [injection Eq as <- <-; piv_acs|]). destruct Hin. }
  assert (RL3 : forall r0 e0, In (r0, e0) pib_RL -> YK11.getr regs3 r0 = sv_denot E e0).
  { intros r0 e0 Hin. rewrite (fsw_pres (ms_regs ms2) regs3 r0 HPsw (HRLcs r0 e0 Hin)).
    apply RGf. unfold piv_regs_E. apply in_or_app. right. exact Hin. }
  assert (G2' : YK11.getr regs3 2 = YK11.getr (ms_regs ms2) 2) by exact (fsw_pres _ _ 2%bv HPsw ltac:(piv_acs)).
  assert (G9' : YK11.getr regs3 9 = YK11.getr (ms_regs ms2) 9) by exact (fsw_pres _ _ 9%bv HPsw ltac:(piv_acs)).
  assert (G19' : YK11.getr regs3 19 = YK11.getr (ms_regs ms2) 19) by exact (fsw_pres _ _ 19%bv HPsw ltac:(piv_acs)).
  assert (G3' : YK11.getr regs3 3 = YK11.getr (ms_regs ms2) 3) by exact (fsw_pres _ _ 3%bv HPsw ltac:(piv_acs)).
  assert (G4' : YK11.getr regs3 4 = YK11.getr (ms_regs ms2) 4) by exact (fsw_pres _ _ 4%bv HPsw ltac:(piv_acs)).
  assert (HRP3 : pib_regsP B regs q v regs3 pib_RL).
  { split; [unfold spZ; rewrite G2', G2; exact E2u|].
    split; [rewrite G9', G9, E9; reflexivity|]. split; [rewrite G19', G19, E19; reflexivity|].
    split; [rewrite G3', G3; exact E3|]. split; [rewrite G4', G4; exact E4|].
    apply (piv_RL_restate E regs3 RL3); [reflexivity | rewrite G9', G9, E9; reflexivity
      | rewrite G19', G19, E19; reflexivity | exact E32]. }
  assert (XR3 : forall j, (j < 13)%nat -> ew E (xatom (3 + j)) = nth j xr (Z_to_bv 64 0))
    by (intros j Hj; rewrite EXn; exact (XR j Hj)).
  assert (HRfr : region_ok tfibsegs E (mrestrict (w_H W') (ms_mem ms2))
    (YP09.mkRegion (Some 2%nat) 0 144 0 0 pib_csL)) by exact (fsw_region_nth E _ _ 1 _ HS2r HmE1).
  assert (HFL2 : pib_frameL (mrestrict (w_H W') (ms_mem ms2)) (spZ regs) xr q v)
    by exact (piv_frameL_of E _ (spZ regs) xr q v pib_csL Hxl E2u E9 E19 E32 XR3 ltac:(lia) ltac:(lia) HRfr
      (incl_refl _)).
  assert (HFL3 : pib_frameL (mrestrict (w_H W3) mem3) (spZ regs) xr q v).
  { apply (piv_frameL_mb (mrestrict (w_H W') (ms_mem ms2))); [|exact HFL2].
    intros zf Hzf. exact (proj1 (QWK zf ltac:(unfold spZ; rewrite G2, E2u; lia) ltac:(lia))). }
  (* ---- v across skip_ws ---- *)
  assert (VK : forall z, v <= z < v + 56 ->
    mrestrict (w_H W3) mem3 (Z_to_bv 64 z) = mrestrict (w_H W') (ms_mem ms2) (Z_to_bv 64 z)).
  { intros z Hz.
    refine (proj2 (fsw_journal_kept_byte B _ _ _ ly' S' (Uc ++ [(a - HEAD, HEAD)]) W' (ms_mem ms2)
      (with_vm_backing (m_vm_lazy md') mat2 md') ly3 S3 (Uc ++ [(a - HEAD, HEAD)]) W3 mem3 md3 0 z HJsw HARU2 OKsw POsw
      _ (pim_inFP_nil z))).
    destruct K9 as [[((cid & pos & Hin & Hc & H8 & H1 & H2) & _)|((b0 & m0 & Hb0 & H1 & H2) & _)] _].
    - right. exists cid, pos. split; [exact Hin | lia].
    - left. exists b0, m0. split; [exact Hb0 | unfold HEAD in H1; lia]. }
  assert (HPO3 : pobj tfibsegs B ly3 S3 W3 mem3 v).
  { apply (pobj_kept_call B _ _ [] ly' S' (Uc ++ [(a - HEAD, HEAD)]) W' (ms_mem ms2)
      (with_vm_backing (m_vm_lazy md') mat2 md') ly3 S3 _ W3 mem3 md3 0 v HJsw HARU2 OKsw POsw);
      [intros z Hz; exact (pim_inFP_nil z) | intros z0 Hz0; destruct (pim_inFP_nil z0 Hz0) | | exact K9].
    intros r0 Hr0. destruct (K7 r0 Hr0) as (H16 & m0 & Hm0 & Hrq). split; [exact H16|]. exists m0.
    split; [rewrite QAB; exact Hm0 | exact Hrq]. }
  assert (HHDR3 : PjStruct.pj_hdr tfibsegs (mrestrict (w_H W3) mem3) v 6 0 0 kids keys (Z.of_nat (length dn)) cap).
  { apply (PjStruct.pj_hdr_eq tfibsegs (mrestrict (w_H W') (ms_mem ms2))); [exact K10|].
    intros z Hz. exact (piv_word_eq _ _ (fun z0 => v <= z0 < v + 56) z VK Hz). }
  (* ---- the resume at 0x850bc ---- *)
  cbn [length Z.of_nat] in QIN. rewrite Z.add_0_r in QIN.
  set (EF := Ereg regs3 (fs_extraT ++ xs)) in *.
  assert (Hrefl : aregs_preserved regs3 regs3) by (intros r0 Hr0; reflexivity).
  destruct (piv_env_at B k S regs q ot v ms Hk HDEP regs3 regs3 xs pib_RL HRP3 Hrefl)
    as (F9 & F19 & F32 & F2u & F3 & F4).
  fold EF in F9, F19, F32, F2u, F3, F4.
  assert (FXn : forall j, ew EF (xatom j) = nth j xs (Z_to_bv 64 0)) by (intros j; unfold EF; apply fsw_ew_xatom).
  assert (Fx0 : ew EF (xatom 0) = Z_to_bv 64 (pc + Z.of_nat (length kk) + 2)) by (rewrite FXn; exact X0).
  assert (Fx1 : ew EF (xatom 1) = Z_to_bv 64 (text + len)) by (rewrite FXn; exact X1).
  assert (Fx2 : ew EF (xatom 2) = Z_to_bv 64 (dd + 1)) by (rewrite FXn; exact X2).
  assert (Fx16 : ew EF (xatom 16) = Z_to_bv 64 kids) by (rewrite FXn; exact X16).
  assert (Fx17 : ew EF (xatom 17) = Z_to_bv 64 keys) by (rewrite FXn; exact X17).
  assert (Fx18 : ew EF (xatom 18) = Z_to_bv 64 (Z.of_nat (length dn))) by (rewrite FXn; exact X18).
  assert (Fx19 : ew EF (xatom 19) = Z_to_bv 64 cap) by (rewrite FXn; exact X19).
  assert (Fx20 : ew EF (xatom 20) = Z_to_bv 64 a) by (rewrite FXn; exact X20).
  assert (Fx21 : ew EF (xatom 21) = Z_to_bv 64 (Z.of_nat (length kk))) by (rewrite FXn; exact X21).
  assert (Fx23 : ew EF (xatom 23) = Z_to_bv 64 (kids + 56 * Z.of_nat (length dn))) by (rewrite FXn; exact X23).
  assert (F9u : bv_unsigned (ew EF 9) = q) by (rewrite F9; apply wz; lia).
  assert (F19u : bv_unsigned (ew EF 19) = v) by (rewrite F19; apply wz; lia).
  assert (Fx0u : bv_unsigned (ew EF (xatom 0)) = pc + Z.of_nat (length kk) + 2) by (rewrite Fx0; apply wz; lia).
  assert (Fx23u : bv_unsigned (ew EF (xatom 23)) = kids + 56 * Z.of_nat (length dn)) by (rewrite Fx23; apply wz; lia).
  assert (Hv8 : v mod 8 = 0) by (destruct HPO0 as [[(_ & Hm8 & _)|(_ & Hm8 & _)] _]; exact Hm8).
  assert (Hvimgh : piv_hide (v + 56 <= 0x10000 \/ FS_IMG_END <= v))
    by exact (fsw_pobj_off_img B ly S W (unpoison U mem) md mem v (proj1 (proj1 (proj1 HPRE))) HPO0).
  assert (HCS : Forall (YP09.chunk_ok tfibsegs EF (mrestrict (w_H W3) mem3) (spZ regs - 144)) pib_csL).
  { apply (piv_csL_ok EF _ (spZ regs) xr q v Hxl); [|exact F9 | exact F19 | exact F32 | lia | lia | lia | exact HFL3].
    intros j Hj. rewrite FXn. exact (XR j Hj). }
  assert (HQR : region_ok tfibsegs EF (mrestrict (w_H W3) mem3) pi_qR)
    by exact (pis_q_ok EF _ q text len (pc + Z.of_nat (length kk) + 2) (dd + 1) tb F9u Fx0 Fx1 Fx2 QIN).
  assert (HVR : region_ok tfibsegs EF (mrestrict (w_H W3) mem3) pib_vR)
    by exact (piv_vR_ok EF _ v 0 0 kids keys (Z.of_nat (length dn)) cap F19u Fx16 Fx17 Fx18 Fx19 ltac:(lia)
      ltac:(lia) (proj2 HPO3) HHDR3).
  assert (HPD : pairwise_disjoint EF (fsT_ret_regions 144 pib_csL pib_rs))
    by exact (piv_disj EF (spZ regs - 144) q v F2u F9u F19u ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
      Hvimgh).
  assert (HGF : atoms_ok EF pib_gfP).
  { apply (piv_gfP_ok EF q v (pc + Z.of_nat (length kk) + 2) (text + len) (dd + 1) kids keys
      (Z.of_nat (length dn)) cap a (Z.of_nat (length kk)) F9u F19u Fx0 Fx1 Fx2 Fx16 Fx17 Fx18 Fx19 Fx20 Fx21);
      try lia; try assumption. }
  assert (HARU3 : ARU tfibsegs B ly3 S3 (Uc ++ [(a - HEAD, HEAD)]) W3 mem3 md3)
    by (split; [exact (proj1 HJsw) | split; [exact OKsw | exact POsw]]).
  assert (Hsp2 : spZ (ms_regs ms2) = spZ regs - 144) by (unfold spZ at 1; rewrite G2; exact E2u).
  assert (HSW144 : STK_skip_ws + 144 <= STK_parse_items (1 - k))
    by (unfold STK_parse_items, STK_parse_items_of, zmaxl, FRAME_parse_items; cbn [fold_right]; lia).
  destruct (pic_after_callT B STKt ot FP [] ly S U _ mem md _ ly' S' (Uc ++ [(a - HEAD, HEAD)]) (ms_mem ms2) _
    (rd_ev T + EV_fuzz_malloc) STK_skip_ws [] (spZ regs) 144 (ms_regs ms2) ly3 S3 (Uc ++ [(a - HEAD, HEAD)]) W3
    regs3 mem3 md3 0 xs pib_csL pib_rs pib_gfP 0x850bc (proj1 HSS) (proj2 HSS) HJ2b HARU2 HJsw
    ltac:(intros z0 Hz0; exfalso; exact (pim_inFP_nil z0 Hz0)) OKsw POsw HPsw
    Hsp2 ltac:(lia) ltac:(vm_compute; discriminate)
    ltac:(rewrite Hsp2, Zminus_mod, Hsp16; reflexivity) ltac:(lia)
    ltac:(unfold STKt; lia)
    piv_wf HCS ltac:(constructor; [exact HQR | constructor; [exact HVR | constructor]]) HPD HGF)
    as (HJ3 & HARU3b & HSTF).
  (* ---- the start state of segment F ---- *)
  pose proof (fsw_ablock_off_img B lyc Sc W1 (unpoison Uc memC) mdC _ _ HAR HinT1) as HTimg.
  rewrite (piv_req tcap) in HTimg by lia.
  assert (HTimgh : piv_hide (text + tcap <= 65536 \/ 6279168 <= text - 16))
    by (unfold piv_hide; destruct HTimg as [Hz|Hz]; [left | right]; unfold FS_IMG_END, HEAD in *; lia).
  clear HTimg.
  set (MF := restrict (w_H W3) (mkst regs3 (Z_to_bv 64 0x850bc) mem3 (seg_rom tfibsegs))) in *.
  assert (HF1 : st_ok tfibsegs EF (pik_setm (fss_retT 0x850bc 144 pib_csL pib_rs pib_gfP)
    (pib_rgs pib_csL pib_RO (0, 24) pib_RO)) MF)
    by exact (pik_st_ok_setm EF _ _ _ HSTF piv_submem_F piv_wf_F).
  assert (HF2 : st_ok tfibsegs EF (pik_setr (pik_setm (fss_retT 0x850bc 144 pib_csL pib_rs pib_gfP)
    (pib_rgs pib_csL pib_RO (0, 24) pib_RO)) pib_RL) MF).
  { apply pik_st_ok_setr; [exact HF1|]. cbn [ms_regs mkst restrict].
    exact (piv_setr_RL regs3 regs3 xs HRP3 Hrefl). }
  destruct (piv_txt_bytes k S regs ot text len tb ms Hk HDEP (mrestrict (w_H W3) mem3) q
    (pc + Z.of_nat (length kk) + 2) (dd + 1) [58] (wsp ++ R0) QIN HRc) as (Hbs & Hbm).
  assert (RTR : region_ok tfibsegs EF (mrestrict (w_H W3) mem3) (pik_treg (xatom 0) 0 [58])).
  { apply (pik_treg_ok EF _ (xatom 0) (pc + Z.of_nat (length kk) + 2) 0 [58] Fx0u ltac:(lia) ltac:(lia)
      ltac:(cbn; lia) Hbs).
    intros i0 Hi0. rewrite Z.add_0_r. exact (Hbm i0 Hi0). }
  assert (DJ2 : all_disjoint EF (pik_treg (xatom 0) 0 [58]) (pib_rgs pib_csL pib_RO (0, 24) pib_RO)).
  { apply all_disjoint_of_extents.
    unfold pib_rgs, pik_treg, pib_RO, fs_got_region, fs_bcell_region, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val fst snd length Z.of_nat Pos.of_succ_nat].
    rewrite Fx0u, F2u, F9u, F19u.
    unfold tfib_D_GOT_asan_shadow_memory_dynamic_address, tfib_D_asan_shadow_memory_dynamic_address, FS_IMG_END,
      HEAD in *.
    cbn [zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat match goal with |- _ /\ _ => split end; try exact I; piv_pd. }
  assert (HF3 : st_ok tfibsegs EF (pik_addr (pik_setr (pik_setm (fss_retT 0x850bc 144 pib_csL pib_rs pib_gfP)
    (pib_rgs pib_csL pib_RO (0, 24) pib_RO)) pib_RL) [pik_treg (xatom 0) 0 [58]]) MF).
  { unfold pik_addr. cbn [app]. apply st_ok_add_region';
      [exact HF2 | apply pik_treg_wf; lia | unfold MF; rewrite restrict_mem; cbn [ms_mem mkst]; exact RTR | exact DJ2]. }
  assert (HATF : atoms_ok EF pib_gf_vk).
  { unfold pib_gf_vk. cbn [atoms_ok]. split; [|exact I]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Fx23u. change (2 ^ 3) with 8. split; [lia|]. split; [|lia].
    clear - Kal Hn0. Z.div_mod_to_equations. lia. }
  assert (HCDF : conds_ok EF (pib_c_m56 :: pib_geu (xatom 23) (xatom 16) :: pib_wsc0)).
  { cbn [conds_ok]. split; [exact (piv_c_m56_ok EF (Z.of_nat (length dn)) Fx18 ltac:(lia))|].
    split; [exact (piv_geu_ok EF (xatom 23) (xatom 16) (kids + 56 * Z.of_nat (length dn)) kids Fx23 Fx16 ltac:(lia)
      ltac:(lia) ltac:(lia))|].
    exact (piv_wsc0_ok EF (pc + Z.of_nat (length kk) + 2) (text + len) Fx0 Fx1 ltac:(lia) ltac:(lia) ltac:(lia)). }
  assert (HALF : alias_ok EF [pib_al_vk])
    by exact (piv_al_vk_ok EF kids (Z.of_nat (length dn)) Fx16 Fx18 ltac:(lia) ltac:(lia) ltac:(lia) Fx23).
  assert (HSF : st_ok tfibsegs EF pib_ss_F MF)
    by (apply pik_st_ok_addf; [exact HF3 | exact HATF | exact HCDF | exact HALF]).
  (* ---- the shadow entries and the write permissions of segment F ---- *)
  assert (UBxF : YP0e.U EF fs_Bx = SHADOW_OFF) by (unfold fs_Bx; apply U_atom; [exact F32 | unfold SHADOW_OFF; lia]).
  assert (HH3 : FSupoisonU.fs_heads B ly3 S3 (Uc ++ [(a - HEAD, HEAD)])).
  { intros r0 Hr0. destruct (K7 r0 Hr0) as (H16 & m0 & Hm0 & Hrq). split; [exact H16|]. exists m0.
    split; [rewrite QAB; exact Hm0 | exact Hrq]. }
  pose proof QTX as (_ & HRBT3 & _). pose proof HRBT3 as (HinT3 & _).
  pose proof HJ3 as (_ & Hly3 & _).
  pose proof Hly3 as (_ & _ & _ & _ & _ & _ & _ & _ & Htop3 & Hslo3 & Hshi3 & _).
  assert (SHOKF : sh_ok tfibsegs fs_Bx pib_SHc EF (mrestrict (w_H W3) mem3)).
  { unfold sh_ok, pib_SHc, pib_SHm. repeat apply Forall_cons; try apply Forall_nil.
    - apply (piv_sh_blk B k S regs ot ms Hk HDEP ly3 S3 (Uc ++ [(a - HEAD, HEAD)]) W3 mem3 md3 EF (xatom 0)
        (text - HEAD) (tcap + HEAD) (pc + Z.of_nat (length kk) + 2) 0 1 HARU3 HH3 HinT3);
        [unfold HEAD in *; lia | lia | unfold HEAD in *; lia | exact UBxF |].
      apply U_atom; [exact Fx0 | lia].
    - apply (piv_sh_q B k ly S U W regs mem md q ot text len p tb ms ch Hk HPRE HWIN HQ16 HIN0 HDEP ly3 S3
        (Uc ++ [(a - HEAD, HEAD)]) W3 mem3 md3 EF 9 HARU3 Hslo3 Hshi3 UBxF).
      apply U_atom; [exact F9 | lia].
    - apply (piv_sh_v B k S regs ot v ms Hk HDEP ly3 S3 (Uc ++ [(a - HEAD, HEAD)]) W3 mem3 md3 EF 19 HARU3 HPO3
        UBxF).
      apply U_atom; [exact F19 | lia]. }
  assert (AWRF : awr_ok tfibsegs B EF (ss_mem pib_ss_F) STKt ot FP (ablocks B ly S) (ablocks B ly3 S3) ly3 []
    (frames S)).
  { assert (HmFs : ss_mem pib_ss_F = [pik_treg (xatom 0) 0 [58]; YP09.mkRegion (Some 2%nat) 0 144 0 0 pib_csL;
      fs_got_region; fs_bcell_region 32; YP09.mkRegion (Some 9%nat) 0 24 0 24 (YP09.r_chunks pi_qR);
      YP09.mkRegion (Some 19%nat) 0 56 0 0 pib_vch]) by reflexivity.
    rewrite HmFs.
    apply awr_ok_cons_ro; [cbn [pik_treg YP09.r_wlo YP09.r_whi]; lia|].
    apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|].
    apply awr_ok_cons_ro; [cbn [fs_got_region YP09.r_wlo YP09.r_whi]; lia|].
    apply awr_ok_cons_ro; [cbn [fs_bcell_region YP09.r_wlo YP09.r_whi]; lia|].
    eapply awr_ok_cons_stack_off with (n := 9%nat) (d := q - ot);
      [reflexivity | cbn [YP09.r_base base_val]; rewrite F9u; lia | cbn [YP09.r_wlo]; unfold STKt; lia
      | cbn [YP09.r_whi]; lia |].
    apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]. apply awr_ok_nil. }
  (* ---- the run of segment F ---- *)
  destruct piv_fin_F as (HpcF & HobF & HresF & HjF & HregsF & Hr11F & HmF4 & HmF1 & HKF).
  eapply (fsw_run_tok_AJU B pitems_tbl pitems_tbl_ok W3 FUEL EF (run_K 0 fs_Bx pib_SHc pib_ss_F) fs_Bx fs_Bspan
    pib_SHc pib_ss_F pib_st_F (TS_stopped SR_fetch) (mkst regs3 (Z_to_bv 64 0x850bc) mem3 (seg_rom tfibsegs))
    STKt ot FP ly S W (unpoison U mem) md [] ly3 S3 (Uc ++ [(a - HEAD, HEAD)]) md3 _ Qc
    HSF SHOKF pib_static_F pib_run_F I HARU3 HJ3 ltac:(rewrite HobF; constructor) AWRF).
  intros ws2 ms5 mat5 Hlen5 HS5 SHOK5 HJ5 HARU5 HFm5 HFr5 HGr5.
  (* ---- the stop of segment F: the memset call ---- *)
  rewrite HjF in Hlen5.
  set (md5 := with_vm_backing (m_vm_lazy md3) mat5 md3) in *.
  set (E5 := extK EF (run_K 0 fs_Bx pib_SHc pib_ss_F) ws2) in *.
  assert (EK : forall nn, (nn < 57)%nat -> ew E5 nn = ew EF nn)
    by (intros nn Hnn; unfold E5; rewrite HKF; apply piv_ew_extK; lia).
  pose proof (piv_regs_of_stop E5 _ ms5 (w_H W3) _ HS5 HregsF) as RG5. rewrite Forall_forall in RG5.
  assert (RGf5 : forall r0 e0, In (r0, e0) piv_regs_F -> YK11.getr (ms_regs ms5) r0 = sv_denot E5 e0)
    by (intros r0 e0 Hin; exact (RG5 (r0, e0) Hin)).
  pose proof (RGf5 1%bv (SLit 0x85170) ltac:(unfold piv_regs_F; cbn [In app]; tauto)) as S1r.
  pose proof (RGf5 2%bv (SOff 2 0) ltac:(unfold piv_regs_F; cbn [In app]; tauto)) as S2r.
  pose proof (RGf5 3%bv (SOff 3 0) ltac:(unfold piv_regs_F; cbn [In app]; tauto)) as S3r.
  pose proof (RGf5 4%bv (SOff 4 0) ltac:(unfold piv_regs_F; cbn [In app]; tauto)) as S4r.
  pose proof (RGf5 9%bv (SOff 9 0) ltac:(unfold piv_regs_F; cbn [In app]; tauto)) as S9r.
  pose proof (RGf5 10%bv (SOff (xatom 23) 0) ltac:(unfold piv_regs_F; cbn [In app]; tauto)) as S10r.
  pose proof (RGf5 12%bv (SLit 56) ltac:(unfold piv_regs_F; cbn [In app]; tauto)) as S12r.
  pose proof (RGf5 19%bv (SOff 19 0) ltac:(unfold piv_regs_F; cbn [In app]; tauto)) as S19r.
  rewrite fsw_SOff0 in S2r, S3r, S4r, S9r, S10r, S19r.
  rewrite EK in S2r, S3r, S4r, S9r, S19r by lia. rewrite EK in S10r by (unfold xatom; lia).
  assert (S11r : YK11.getr (ms_regs ms5) 11 = w64 0).
  { rewrite (st_ok_restrict_reg tfibsegs (w_H W3) E5 _ ms5 11%bv HS5), Hr11F.
    pose proof (piv_c_m56_ok EF (Z.of_nat (length dn)) Fx18 ltac:(lia)) as Hc.
    unfold acond_ok, pib_c_m56 in Hc. cbn [ac_c ac_a ac_b] in Hc. rewrite branch_eq_U in Hc.
    apply Z.eqb_eq in Hc. rewrite U_SLit in Hc. change (zcanon 0) with 0 in Hc.
    rewrite (pik_sv_denot_agree E5 EF); [| unfold E5; apply piv_ed_extK |].
    - apply bv_eq. unfold w64. rewrite (unsigned_lit_small 0) by lia. exact Hc.
    - intros nn Hnn. cbn [pik_sv_atoms app] in Hnn.
      repeat (destruct Hnn as [<-|Hnn]; [apply EK; unfold xatom; lia|]). destruct Hnn. }
  assert (HRAW5 : forall z, 0 <= z < 2 ^ 64 -> ~ (q <= z < q + 24) ->
    mrestrict (w_H W3) (ms_mem ms5) (Z_to_bv 64 z) = mrestrict (w_H W3) mem3 (Z_to_bv 64 z)).
  { intros z Hz Hnz. apply HFr5. rewrite wz by lia. intros Hw. apply piv_wr_F in Hw. rewrite F9u in Hw. lia. }
  pose proof HARU2 as (HAR2 & _ & _).
  (* ---- the bytes of the live list and of v, from the store to the memset call ---- *)
  set (L2 := (parse_items_shape.pis_slots true kids keys cap ++ Di) ++ [(a, Z.of_nat (length kk) + 1)]) in *.
  assert (KB5 : forall p0 k0 z, In (p0, k0) L2 -> p0 - HEAD <= z < p0 + k0 ->
    mrestrict (w_H W3) (ms_mem ms5) (Z_to_bv 64 z) = mrestrict (w_H W') (ms_mem ms2) (Z_to_bv 64 z)).
  { intros p0 k0 z Hin Hz. pose proof (K1 p0 k0 Hin) as RB. pose proof RB as (RBin & _ & Rk0 & _).
    destruct (fsw_rblock_low B ly' S' W' (unpoison (Uc ++ [(a - HEAD, HEAD)]) (ms_mem ms2)) _ (ms_mem ms2) p0 k0
      HAR2 RB) as (Rl & Rh).
    rewrite (HRAW5 z ltac:(lia) ltac:(lia)).
    refine (proj2 (fsw_journal_kept_byte B _ _ _ ly' S' (Uc ++ [(a - HEAD, HEAD)]) W' (ms_mem ms2) _ ly3 S3
      (Uc ++ [(a - HEAD, HEAD)]) W3 mem3 md3 0 z HJsw HARU2 OKsw POsw _ (pim_inFP_nil z))).
    left. exists (p0 - HEAD), (k0 + HEAD). split; [exact RBin | rewrite piv_req by lia; unfold HEAD in *; lia]. }
  assert (VK5 : forall z, v <= z < v + 56 ->
    mrestrict (w_H W3) (ms_mem ms5) (Z_to_bv 64 z) = mrestrict (w_H W') (ms_mem ms2) (Z_to_bv 64 z))
    by (intros z Hz; rewrite (HRAW5 z ltac:(lia) ltac:(lia)); exact (VK z Hz)).
  assert (BL5 : rd_blocks_ok tfibsegs B ly3 S3 W3 (ms_mem ms5) L2).
  { intros p0 k0 Hin. pose proof (K1 p0 k0 Hin) as (RBin & Ral & Rk & Rv).
    split; [rewrite QAB; exact RBin|]. split; [exact Ral|]. split; [exact Rk|].
    intros j Hj. unfold mbyte. rewrite (KB5 p0 k0 (p0 - HEAD + Z.of_nat j) Hin ltac:(unfold HEAD in *; lia)).
    exact (Rv j Hj). }
  assert (TX5 : rd_text tfibsegs B ly3 S3 W3 (ms_mem ms5) text len tcap).
  { pose proof QTX as (T1 & T2 & T3). split; [exact T1|]. split; [|exact T3].
    apply (pio_rblock_keep B ly3 S3 W3 mem3 (ms_mem ms5) text tcap T2).
    intros z Hz. apply HRAW5; lia. }
  assert (HDR5 : PjStruct.pj_hdr tfibsegs (mrestrict (w_H W3) (ms_mem ms5)) v 6 0 0 kids keys (Z.of_nat (length dn))
    cap).
  { apply (PjStruct.pj_hdr_eq tfibsegs (mrestrict (w_H W') (ms_mem ms2))); [exact K10|].
    intros z Hz. exact (piv_word_eq _ _ (fun z0 => v <= z0 < v + 56) z VK5 Hz). }
  assert (PO5 : pobj tfibsegs B ly3 S3 W3 (ms_mem ms5) v).
  { apply (pio_pobj_xfer B ly3 S3 W3 mem3 (ms_mem ms5) v HPO3).
    - intros z Hz. apply pio_aview_raw.
      assert (Hzr : 0 <= z < alloc_ceiling) by (clear - Hz Hv1 Hv2; lia).
      destruct (pio_shadow_rng z Hzr) as (Hs1 & Hs2). apply HRAW5; clear - Hs2 Hqc Hac47; lia.
    - intros i0 Hi0. apply (writable_at_eq tfibsegs (mrestrict (w_H W3) mem3)); [apply HRAW5; clear - Hi0 Hv1 Hv2 Hqc Hac47; lia|].
      exact (proj2 HPO3 i0 Hi0). }
  assert (OP5 : parse_items_shape.pis_open tfibsegs (mrestrict (w_H W3) (ms_mem ms5)) (ReaderRes.lin L2) v true 0
    kids keys cap (Z.of_nat (length dn)) (map snd dn) (map fst dn) Di).
  { apply (parse_items_shape.pis_frame tfibsegs _ _ _ _ v true 0 kids keys cap (Z.of_nat (length dn)) (map snd dn)
      (map fst dn) Di 0 (Z.of_nat (length dn)) K11 HDR5 ltac:(lia)
      (parse_items_shape.pis_open_lblk tfibsegs _ _ _ _ _ _ _ _ _ _ _ _ K11)).
    intros z Hz. rewrite length_map in Hz.
    destruct (pio_ifoot_in kids keys cap (Z.of_nat (length dn)) Di z ltac:(lia) Hz) as ([p0 k0] & Hb & Hh).
    unfold PjStruct.pj_holds in Hh. cbn [fst snd] in Hh.
    assert (Hz5 := KB5 p0 k0 z ltac:(unfold L2; apply in_or_app; left; exact Hb) ltac:(unfold HEAD in *; lia)).
    split; [exact (pio_mbyte_raw _ _ z Hz5) | intros Hw; exact (writable_at_eq tfibsegs _ _ z Hz5 Hw)]. }
  assert (U5 : PjStruct.pj_u64 tfibsegs (mrestrict (w_H W3) (ms_mem ms5)) (keys + 8 * Z.of_nat (length dn)) a).
  { apply (PjStruct.pj_u64_eq tfibsegs (mrestrict (w_H W') (ms_mem ms2))); [exact K12|].
    intros z Hz. apply (piv_word_eq _ _ (fun z0 => keys + 8 * Z.of_nat (length dn) <= z0 <
      keys + 8 * Z.of_nat (length dn) + 8) z); [|exact Hz].
    intros z0 Hz0. apply (KB5 keys (8 * cap)); [unfold L2; apply in_or_app; left; exact HinYL | unfold HEAD; lia]. }
  assert (C5 : PjStruct.pj_cstr tfibsegs (mrestrict (w_H W3) (ms_mem ms5)) (ReaderRes.lin L2) a
    (Z.of_nat (length kk) + 1) kk).
  { apply (PjStruct.pj_cstr_eq tfibsegs (mrestrict (w_H W') (ms_mem ms2)) (ReaderRes.lin L2)); [exact K13 | |].
    - unfold ReaderRes.lin. unfold L2. apply in_or_app. right. left. reflexivity.
    - intros z Hz. unfold PjStruct.pj_holds in Hz. cbn [fst snd] in Hz.
      apply (piv_word_eq _ _ (fun z0 => a <= z0 < a + (Z.of_nat (length kk) + 1)) z); [|exact Hz].
      intros z0 Hz0. apply (KB5 a (Z.of_nat (length kk) + 1));
        [unfold L2; apply in_or_app; right; left; reflexivity | unfold HEAD; lia]. }
  (* ---- struct pj_in past `:` (the stop's q region) ---- *)
  assert (RQ5 : region_ok tfibsegs E5 (mrestrict (w_H W3) (ms_mem ms5)) (YP09.mkRegion (Some 9%nat) 0 24 0 24
    [YP09.mkChunk 0 (CVal 8 (SOff (xatom 0) 1)); YP09.mkChunk 8 (CVal 8 (SOff (xatom 1) 0));
     YP09.mkChunk 16 (CVal 4 (SOff (xatom 2) 0))])) by exact (fsw_region_nth E5 _ _ 4 _ HS5 HmF4).
  assert (E59u : bv_unsigned (ew E5 9) = q) by (rewrite EK by lia; exact F9u).
  pose proof (fsw_field E5 _ 9 q _ 0 24 0 24 0 8 (SOff (xatom 0) 1) (pc + Z.of_nat (length kk) + 2 + 1) RQ5 E59u
    ltac:(cbn; tauto) ltac:(apply piv_den_off; [rewrite EK by (unfold xatom; lia); exact Fx0 | lia | lia | lia])
    ltac:(cbn; lia) ltac:(cbn; lia)) as Fq0.
  pose proof (fsw_field E5 _ 9 q _ 0 24 0 24 8 8 (SOff (xatom 1) 0) (text + len) RQ5 E59u
    ltac:(cbn; tauto) ltac:(rewrite fsw_SOff0; rewrite EK by (unfold xatom; lia); exact Fx1) ltac:(cbn; lia)
    ltac:(cbn; lia)) as Fq8.
  pose proof (fsw_field E5 _ 9 q _ 0 24 0 24 16 4 (SOff (xatom 2) 0) (dd + 1) RQ5 E59u
    ltac:(cbn; tauto) ltac:(rewrite fsw_SOff0; rewrite EK by (unfold xatom; lia); exact Fx2) ltac:(cbn; lia)
    ltac:(cbn; lia)) as Fq16.
  rewrite Z.add_0_r in Fq0.
  pose proof RQ5 as (_ & _ & RQW & _). cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in RQW. rewrite E59u in RQW.
  assert (HIN5 : PjIn.pj_in_ok tfibsegs (mrestrict (w_H W3) (ms_mem ms5)) q text len (pc + Z.of_nat (length kk) + 3)
    (dd + 1) tb).
  { pose proof QIN as (_ & _ & _ & _ & I5 & I6 & I7 & _ & I9 & I10 & I11 & I12).
    refine (conj _ (conj _ (conj _ (conj _ (conj I5 (conj I6 (conj I7 (conj _ (conj I9 (conj _ (conj I11 I12))))))))))).
    - replace (pc + Z.of_nat (length kk) + 3) with (pc + Z.of_nat (length kk) + 2 + 1) by lia.
      exact (proj2 (fsw_val_pj_u64 _ _ q _ Fq0 ltac:(lia) ltac:(lia) ltac:(lia))).
    - exact (proj2 (fsw_val_pj_u64 _ _ (q + 8) _ Fq8 ltac:(lia) ltac:(lia) ltac:(lia))).
    - exact (proj1 (fsw_pj_word4_iff tfibsegs _ (q + 16) (dd + 1) ltac:(lia) ltac:(lia)) Fq16).
    - split; [lia|]. split; [lia|]. intros o Ho. exact (RQW o Ho).
    - lia.
    - apply (pim_eqon_bytes (mrestrict (w_H W3) mem3)); [|exact I10].
      intros z Hz. apply HRAW5; clear - Hz Htblen Ht0b Htx3 Htx4 Hqc Hac47; lia. }
  (* ---- the frame chain at q, the caller's window, the frame, the registers ---- *)
  assert (HCH5 : achain ly3 (aview tfibsegs (w_H W3) (unpoison (Uc ++ [(a - HEAD, HEAD)]) (ms_mem ms5))) (spZ regs) q
    chq).
  { apply (piv_chain_kept lyc ly3 _ _ (spZ regs) q (ly_top ly) chq HCH HCHF Htop Htop3).
    intros z Hz Hzq.
    assert (Hz64 : 0 <= z < 2 ^ 64) by lia.
    assert (NS : ~ (SHADOW_OFF <= z < SHADOW_OFF + 2 ^ 44)) by (unfold SHADOW_OFF; lia).
    rewrite (aview_at tfibsegs (w_H W3) _ (ms_mem ms5) z (fsw_unpoison_app B ly3 S3 _ W3 (ms_mem ms5) _ z HARU5 Hz64 NS)).
    rewrite (aview_at tfibsegs (w_H W1) _ memC z (fsw_unpoison_app B lyc Sc Uc W1 memC mdC z HARU Hz64 NS)).
    rewrite (pio_aview_raw (w_H W3) mem3 (ms_mem ms5) z (HRAW5 z Hz64 Hzq)).
    assert (Hsk : aview tfibsegs (w_H W3) mem3 z = aview tfibsegs (w_H W') (ms_mem ms2) z).
    { destruct (Z_lt_le_dec z ot) as [Hzo | Hzo].
      - destruct (QWK z ltac:(rewrite Hsp2; lia) ltac:(lia)) as (Hm & _). unfold aview. rewrite Hm. reflexivity.
      - pose proof HJsw as (_ & _ & _ & _ & _ & _ & _ & _ & J9 & _).
        pose proof (J9 z ltac:(lia) ltac:(lia)) as Hj9.
        rewrite (aview_at tfibsegs (w_H W3) _ mem3 z (fsw_unpoison_app B ly3 S3 _ W3 mem3 md3 z HARU3 Hz64 NS)) in Hj9.
        rewrite (aview_at tfibsegs (w_H W') _ (ms_mem ms2) z
          (fsw_unpoison_app B ly' S' _ W' (ms_mem ms2) _ z HARU2 Hz64 NS)) in Hj9.
        exact Hj9. }
    rewrite Hsk.
    rewrite (pio_aview_raw (w_H W') mem' (ms_mem ms2) z (HRAW z Hz64 ltac:(lia))).
    destruct (Z_lt_le_dec z ot) as [Hzo | Hzo].
    - destruct (HWK' z ltac:(lia) Hzq) as (Hm & _). unfold aview. rewrite Hm. reflexivity.
    - pose proof HJps as (_ & _ & _ & _ & _ & _ & _ & _ & J9 & _).
      pose proof (J9 z ltac:(lia) ltac:(lia)) as Hj9.
      rewrite (aview_at tfibsegs (w_H W') _ mem' z (fsw_unpoison_app B ly' S' _ W' mem' md' z HARU' Hz64 NS)) in Hj9.
      rewrite (aview_at tfibsegs (w_H W1) _ memC z (fsw_unpoison_app B lyc Sc Uc W1 memC mdC z HARU Hz64 NS)) in Hj9.
      exact Hj9. }
  assert (WK5 : wkeep tfibsegs W W3 mem (ms_mem ms5) (spZ regs) ot q 24).
  { apply (piv_wkeep_trans k S W regs mem q ot ms Hk HDEP W1 W3 memC (ms_mem ms5) (spZ regsC) HWK); [|lia].
    intros z Hz Hzq.
    assert (Hz64 : 0 <= z < 2 ^ 64) by lia.
    destruct (HWK' z Hz Hzq) as (M1 & Wr1).
    assert (R2 : mrestrict (w_H W') (ms_mem ms2) (Z_to_bv 64 z) = mrestrict (w_H W') mem' (Z_to_bv 64 z))
      by (apply HRAW; lia).
    destruct (QWK z ltac:(rewrite Hsp2; lia) ltac:(lia)) as (M3 & Wr3).
    pose proof (HRAW5 z Hz64 Hzq) as R5.
    split.
    - rewrite (pio_mbyte_raw _ _ z R5), M3, (pio_mbyte_raw _ _ z R2). exact M1.
    - split; intros Hw.
      + apply (writable_at_eq tfibsegs _ _ z R5). apply (proj1 Wr3).
        apply (writable_at_eq tfibsegs _ _ z R2). exact (proj1 Wr1 Hw).
      + apply (proj2 Wr1). apply (writable_at_eq tfibsegs _ _ z (eq_sym R2)). apply (proj2 Wr3).
        exact (writable_at_eq tfibsegs _ _ z (eq_sym R5) Hw). }
  assert (HFL5 : pib_frameL (mrestrict (w_H W3) (ms_mem ms5)) (spZ regs) xr q v).
  { apply (piv_frameL_mb (mrestrict (w_H W3) mem3)); [|exact HFL3].
    intros z Hz. apply pio_mbyte_raw. apply HRAW5; lia. }
  assert (HRP5 : pib_regsP B regs q v (ms_regs ms5) pib_RL).
  { split; [unfold spZ at 1; rewrite S2r; exact F2u|].
    split; [rewrite S9r, F9; reflexivity|]. split; [rewrite S19r, F19; reflexivity|].
    split; [rewrite S3r; exact F3|]. split; [rewrite S4r; exact F4|].
    apply (piv_RL_restate E5 (ms_regs ms5)).
    - intros r0 e0 Hin. apply RGf5. unfold piv_regs_F. apply in_or_app. right. exact Hin.
    - unfold E5. rewrite piv_ed_extK. reflexivity.
    - rewrite S9r. apply EK. lia.
    - rewrite S19r. apply EK. lia.
    - rewrite EK by lia. exact F32. }
  (* ---- the read-only view and fuzz/alloc.c's statics at the memset call ---- *)
  assert (HRO3 : arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W3) mem3))
    by exact (arodata_kept B _ _ _ ly' S' (Uc ++ [(a - HEAD, HEAD)]) W' (ms_mem ms2) _ ly3 S3 _ W3 mem3 md3 0 HJsw HARU2
       OKsw POsw pis_sink_nil (fun z _ => pim_inFP_nil z) HRO2).
  assert (HRO5 : arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W3) (ms_mem ms5))).
  { apply (pim_ro_keep B (aview tfibsegs (w_H W3) mem3)); [exact HRO3|].
    intros z Hz. destruct (piv_img_lo z (fsw_roP_img z Hz)) as (Hz1 & Hz2). unfold FS_IMG_END in Hz2.
    apply pio_aview_raw. apply HRAW5; clear - Hz1 Hz2 Hqc C1 Hac47; lia. }
  assert (Hheld : PjGrammar.held (T ++ [PjGrammar.EAlloc (Datatypes.S (length kk))]) =
    PjGrammar.held T + (Z.of_nat (length kk) + 1)).
  { rewrite <- K5. unfold L2. rewrite pim_rd_sum_app, HSUM. unfold rd_sum. cbn [fold_right fst snd]. lia. }
  assert (HG5 : fs_glob tfibsegs W3 (ms_mem ms5)
    (live + PjGrammar.held (T ++ [PjGrammar.EAlloc (Datatypes.S (length kk))]))
    (Z.max peak1 (live + PjGrammar.held T + Z.of_nat (length kk) + 1))
    (cnt + Z.of_nat (length (T ++ [PjGrammar.EAlloc (Datatypes.S (length kk))]))) fail).
  { rewrite Hheld, length_app. cbn [length].
    replace (live + (PjGrammar.held T + (Z.of_nat (length kk) + 1)))
      with (live + PjGrammar.held T + Z.of_nat (length kk) + 1) by lia.
    replace (cnt + Z.of_nat (length T + 1)) with (cnt + Z.of_nat (length T) + 1) by lia.
    apply (pim_glob_eqon W3 W3 mem3 (ms_mem ms5)); [|exact QGL].
    intros z Hz. destruct (piv_img_lo z (pim_pstat_img z Hz)) as (Hz1 & Hz2). unfold FS_IMG_END in Hz2.
    apply HRAW5; clear - Hz1 Hz2 Hqc C1 Hac47; lia. }
  assert (HevT : rd_ev (T ++ [PjGrammar.EAlloc (Datatypes.S (length kk))]) = rd_ev T + EV_fuzz_malloc + 0)
    by (rewrite pim_rd_ev_app, pim_rd_ev_alloc; lia).
  assert (Hech : length (flat_map PjRoundTrip.ech kk) = length kk) by (rewrite (pim_ech_plain kk Hplain); reflexivity).
  assert (K2' : Permutation (ablocks B ly3 S3) (ablocks B ly S ++ rd_hblocks L2)) by (rewrite QAB; exact K2).
  unfold L2 in BL5, OP5, C5, K2', K3, K4, K5, K6. rewrite <- !app_assoc in BL5, OP5, C5, K2', K4, K5, K6.
  (* ---- the memset call, and pib_IM there ---- *)
  rewrite (st_ok_restrict_mkst tfibsegs (w_H W3) E5 _ ms5 HS5 HresF), HpcF.
  refine (K (T ++ [PjGrammar.EAlloc (Datatypes.S (length kk))]) ly3 S3 (Uc ++ [(a - HEAD, HEAD)]) W3 (ms_mem ms5)
    md5 (ms_regs ms5) chq (pc + Z.of_nat (length kk) + 3) (Da ++ [(a, Z.of_nat (length kk) + 1)])
    (Z.max peak1 (live + PjGrammar.held T + Z.of_nat (length kk) + 1)) _).
  unfold pib_IM, pib_IK. cbv zeta.
  split; [|split; [exact S1r | split; [rewrite S10r; exact Fx23 | split; [exact S11r | exact S12r]]]].
  refine (conj Hms (conj _ (conj Hi (conj Hc54 (conj _ (conj HRP5 (conj HFL5 (conj _ (conj HRd (conj _ (conj _
    (conj U5 C5)))))))))))).
  + rewrite Htr, Hech, <- app_assoc. reflexivity.
  + refine (conj _ (conj HARU5 (conj HRO5 HH3))). rewrite HevT. exact HJ5.
  + exact (conj HCH5 (conj HCHF (conj Htop3 (conj HIN5 WK5)))).
  + assert (Hpk' : peak <= Z.max peak1 (live + PjGrammar.held T + Z.of_nat (length kk) + 1)) by lia.
    exact (conj TX5 (conj PO5 (conj BL5 (conj K2' (conj K3 (conj K4 (conj K5 (conj K6 (conj HG5 Hpk'))))))))).
  + exact (conj HDR5 OP5).
Qed.

(* ================= the composition: pib_IE at 0x85048 -> pib_IH at 0x851d0 =================
   segment E, skip_ws #3, segment F (piv_step_EF), the memset and segment G (piv_step_MG), the parse_value (k + 1) call
   (piv_step_V). `Proof using All`: the lemma takes every Section variable and hypothesis, in declaration order, so its
   form after the Section is fixed (the caller, parse_items_holds, passes them explicitly). *)
Lemma piv_val : forall dn kk x rm T lyc Sc Uc (W1 : world tfibsegs) memC mdC regsC chq pc kids keys cap Di Da peak1
    a ly' S' (W' : world tfibsegs) regs' mem' md' (Qc : world tfibsegs -> config -> Prop),
  IE dn kk x rm T lyc Sc Uc W1 memC mdC regsC chq pc kids keys cap Di Da peak1 a ly' S' W' regs' mem' md' ->
  (forall T2 lyc2 Sc2 Uc2 (W2 : world tfibsegs) mem2 md2 regs2 chq2 pc2 Da2 peak2 D Dx ly3 S3 (W3 : world tfibsegs)
      regs3 mem3 md3,
     IH dn kk x rm T2 lyc2 Sc2 Uc2 W2 mem2 md2 regs2 chq2 pc2 kids keys cap Di Da2 peak2 a D Dx ly3 S3 W3 regs3 mem3 md3 ->
     SRr tfibsegs W3 (mkCfg (mkst regs3 (Z_to_bv 64 0x851d0) mem3 (seg_rom tfibsegs)) md3) Qc) ->
  SRr tfibsegs W' (mkCfg (mkst regs' (Z_to_bv 64 0x85048) mem' (seg_rom tfibsegs)) md') Qc.
Proof using All.
intros dn kk x rm T lyc Sc Uc W1 memC mdC regsC chq pc kids keys cap Di Da peak1 a ly' S' W' regs' mem' md' Qc HIE K.
apply (piv_step_EF dn kk x rm T lyc Sc Uc W1 memC mdC regsC chq pc kids keys cap Di Da peak1 a ly' S' W' regs' mem' md'
  Qc HIE).
intros T2 lyc2 Sc2 Uc2 W2 mem2 md2 regs2 chq2 pc2 Da2 peak2 HIM.
apply (piv_step_MG dn kk x rm T2 lyc2 Sc2 Uc2 W2 mem2 md2 regs2 chq2 pc2 kids keys cap Di Da2 peak2 a Qc HIM).
intros mem3 md3 regs3 chq3 HIV.
apply (piv_step_V dn kk x rm T2 lyc2 Sc2 Uc2 W2 mem3 md3 regs3 chq3 pc2 kids keys cap Di Da2 peak2 a Qc HIV).
intros D Dx ly3 S3 W3 regs4 mem4 md4 HIH.
exact (K T2 lyc2 Sc2 Uc2 W2 mem3 md3 regs3 chq3 pc2 Da2 peak2 D Dx ly3 S3 W3 regs4 mem4 md4 HIH).
Qed.

End PI.
