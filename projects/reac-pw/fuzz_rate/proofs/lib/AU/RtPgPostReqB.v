(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of proofs/reac-pw/fuzz_role/lib/A/RPgX01.v at 9bffaa83ff88
   [Apache-2.0] (rx_reg_atom / rx_reg_ext / rx_ew_reg / rx_st_region / rx_chunk_zero / rx_flag0_of, the saved-slot
   chunk list rx_sv_chunks, the numeral tactics z5 / z5g and the flag-store tactic rx_run_flag, which passes
   aj_flag_store its sixteen journal arguments) and of proofs/reac-pw/fuzz_role/lib/A/RPgCheck.v at 77f59d02b018
   [Apache-2.0] (the shape of a `ret` leaf into a callee post), for reac-pw/fuzz_rate's image A: the walk is
   check_csv's release and epilogue, the side-stack class is 2 instead of 3, and the post is RtPgCSpec.rt_cpost_o,
   whose owned-set conjunct is discharged from the cut's layout, chunk and frame equalities. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgCcsvS3.v, with its module names changed; 335 of its 365 lines of code are new or changed and 296 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgPostReq.v at b561c36fcf63; ported to
   reac-pw/fuzz_rate's image A: rate's pcs, registers (s9 = &pp->corrupt, s6 / s7 the shadow byte and the address of
   &pp->len, s10 = len, s2 = K) and 20-entry value list, the tail split at 0x828ac (w10_tail8), the lane kit
   RtPgPostK and RtPgMem's / RtPgSteps' lemmas in place of role's. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgPostReq.v at 8af9cea6f917; ported to image B
   (fuzz_rate.asan-ubsan): image B's pcs and registers (s8 = &pp->corrupt, t2 = &pp->len, s6 = len, s4 = K), the
   tail's shadow address of &pp->len read from the real-frame cell R+0x170 (a region of the engine's state at s1),
   RtPgSegB's 21-entry value list, the 0x220 real frame and the 88-byte frame shadow, the lane kit RtPgPostKB and
   RtPgMemB's / RtPgStepsB's lemmas in place of image A's. *)
(* reac-pw/fuzz_rate image B (fuzz_rate.asan-ubsan, pinned sha256
   c30584a7214902c43e35abebe35194418b7fdefacb6e7ed16fe0492228ec1d14; addresses measured on the unstripped twin
   a1e5fa55ae27e657ea2719297ec4c037110f10fa9047c3ea7bb6ea7fcb358cb1): the end of the build segment of
   LLVMFuzzerTestOneInput (0x8076c), pod.h:447, fuzz_rate.c:245 and fuzz.h:73. Proves no function (kind: segment
   lemma).
   THE CODE
     0x829fc srli a0,s8,3 / add a0,a0,s4 / lb a0,0(a0)     the shadow byte of &pp->corrupt (s8 = pp + 0x4d18)
     0x82a08 bnez a0 -> 0x831b8                             its second test (andi a1,s8,7; addi a1,a1,3; blt a1,a0)
     0x82a0c li a0,1 / 0x82a10 sw a0,0(s8)                  pp->corrupt = 1
     0x82a14 ld a0,0x170(s1) / lbu a0,0(a0)                 the shadow byte of &pp->len (R+0x170 holds its address,
                                                            (pp + 0x4000 >> 3) + K)
     0x82a1c bnez a0 -> 0x834cc                             its error path (mv a0,t2; the report call)
     0x82a20 ld s6,0(t2)                                    len = pp->len (t2 = pp + 0x4000)
     0x82a24 seqz a0,s6 / 0x82a28 add a0,s6,a0              the second request, len + (len == 0)
     0x82a2c jal (the malloc wrapper)                       the cut C2 (rate_build_contract's end), not run here
   Each instrumented check is one shadow obligation of the engine's token path (lib/Reusable/YCbn.v): the 4 bytes at
   &pp->corrupt and the 8 at &pp->len lie in the first block, whose bytes are marked usable (RtPgMemB.rtmb_blk_ra), so
   the error path is not reached. The tail's check loads its shadow address from R+0x170: the engine's state at
   0x82a14 has a region at s1 whose chunk at 0x170 is the shadow expression of t2's atom 7, so the `lbu` is the
   engine's shadow token.
   wb10_tail8: from 0x82a24 (len in s6) to C2;
   wb10_tail: from 0x82a14 (the no-corruption arms of the piece and the corruption's end): the len check and load,
   then wb10_tail8;
   wb10_req: RtPgSegB's rsb_piece_W10_req_stmt, RT -> C2: the store of corrupt = 1, then wb10_tail. *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import Cursor Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import RtPgImgB RtPgMemB RtPgSegB.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import RtPgStepsB RtPgPostKB.
Require OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* image B's loaded segments *)
Local Abbreviation rsegs := OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.M.loaded_segments.

Local Arguments x_STK {segs} _. Local Arguments x_sp0 {segs} _. Local Arguments x_FP {segs} _.
Local Arguments x_ly {segs} _. Local Arguments x_S {segs} _. Local Arguments x_W0 {segs} _.
Local Arguments x_mem0 {segs} _. Local Arguments x_md0 {segs} _. Local Arguments x_own {segs} _.
Local Arguments x_k {segs} _. Local Arguments x_regs {segs} _. Local Arguments x_lyc {segs} _.
Local Arguments x_Sc {segs} _. Local Arguments x_W {segs} _. Local Arguments x_memc {segs} _.
Local Arguments x_mdc {segs} _. Local Arguments x_RLO {segs} _. Local Arguments x_RHI {segs} _.
Local Arguments x_e {segs} _. Local Arguments x_pos {segs} _.

Section r. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.

(* the value of a chunk of a region of a run's state *)
Lemma wb10r_field : forall E m n b cs lo hi wlo whi od (w : N) e v,
  region_ok rsegs E m (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
  bv_unsigned (ew E n) = b -> In (YP09.mkChunk od (CVal w e)) cs -> sv_denot E e = Z_to_bv 64 v ->
  0 <= v < 2 ^ (8 * Z.of_N w) -> (Z.of_N w <= 8) ->
  val_mem rsegs m (b + od) (N.to_nat w) v.
Proof.
intros E m n b cs lo hi wlo whi od w e v HR Hn Hc He Hv Hw.
exact (val_of_chunk_ok rsegs E m b od w e v (rtsb_chunks E m n b cs lo hi wlo whi HR Hn _ Hc) He Hv Hw).
Qed.

(* ---- 0x82a24 -> C2: the second request, len + (len == 0) = len ---- *)
Lemma wb10_tail8 : forall (cx : rsb_scx rsegs) POST rest ly2 S2 (W2 : world rsegs) regs2 mem2 md2,
  rsb_pre rsegs B cx -> rsb_from_C2 rsegs B MT cx POST rest ->
  rsb_core rsegs B MT cx (rsb_E1 rsegs cx) ly2 S2 W2 regs2 mem2 md2 ->
  rsb_at_cx rsegs cx W2 mem2 regs2 (rsb_L_post rsegs cx) ->
  getr regs2 (Z_to_bv 5 22) = w64 (q_len (x_e cx)) ->
  rsb_fsh_at rsegs cx W2 mem2 rsb_P0 ->
  rsb_pp_at rsegs cx W2 mem2 (pp_bytes (fst (pod_build rest))) -> q_len (x_e cx) = rt_len rest ->
  SRr rsegs W2 (cfg_at rsegs 0x82a24 regs2 mem2 md2) POST.
Proof.
intros cx POST rest ly2 S2 W2 regs2 mem2 md2 HP HC2 HC HL H22 Hfsh Hpp Hlen.
pose proof wb10_wx as Hwx. pose proof wb10_segs_low as Hsegs.
pose proof (AR_laws_ok rsegs B) as LAWS.
destruct (wb10_ctx B MT cx ly2 S2 W2 regs2 mem2 md2 HP HC)
  as (Hin & Hfresh & Hal & Hlo & Hhi & Happ & Hpres & H2 & HR16 & HRS & HSTK & Hceil & H47 & HAR).
destruct (wb10_F_ctx B cx HP) as (HF1 & HF2 & HF3).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (wb10_rec_facts rest) as (Hwf & _ & _ & _).
pose proof (rt_len_bounds rest) as HLb. rewrite <- Hlen in HLb.
pose proof HL as HL0.
pose proof HC as (HJ & _).
remember (Ereg regs2 []) as E eqn:HE.
assert (E22 : ew E 22 = Z_to_bv 64 (q_len (x_e cx)))
  by (subst E; rewrite (ew_Ereg_nat regs2 _ 22 (Z_to_bv 5 22) eq_refl); exact H22).
assert (HS : st_ok rsegs E (mkSS 0x82a24 sr_atoms [] None (mkFacts [(22%nat, mkAF 8 5440 0)] [] []))
  (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 0x82a24) mem2 (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. subst E. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor.
  - cbn. tauto.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E22, !unsigned_lit_small by lia.
    repeat match goal with |- _ /\ _ => split end; try exact I; try lia;
    try (rewrite Z.pow_0_r; apply Z.mod_1_r). }
assert (SHOK : sh_ok rsegs WB10Bx [] E (mrestrict (w_H W2) mem2)) by constructor.
unfold cfg_at. change (w64 0x82a24) with (Z_to_bv 64 0x82a24).
aj_run_to_tok wb10_tbl_ok HS HJ SHOK WB10Bspan 0x82a2c.
{ awr_ok_tac. }
(* the run's end, at C2 *)
assert (HK : forall a, 0 <= a < 2 ^ 64 -> aview rsegs (w_H W2) (ms_mem ms) a = aview rsegs (w_H W2) mem2 a).
{ intros a Ha. apply (wb10_frame_kept _ _ _ _ _ HFr a Ha). intros (rg & Hr & _). cbn [ss_mem] in Hr. destruct Hr. }
assert (HAE : env_agree 32 (Ereg regs2 []) E) by (subst E; apply env_agree_refl).
pose proof (regs_kept_of_st_ok rsegs _ _ ms regs2 [] (w_H W2) [Z_to_bv 5 10] HS HAE
  ltac:(vm_compute; reflexivity)) as RK.
assert (R10 : getr (ms_regs ms) (Z_to_bv 5 10) = w64 (q_len (x_e cx))).
{ rewrite (st_ok_restrict_reg rsegs (w_H W2) _ _ ms (Z_to_bv 5 10) HS). wb10_sr_eval.
  exact (wb10_den_atom _ 22 _ E22). }
assert (R22 : getr (ms_regs ms) (Z_to_bv 5 22) = w64 (q_len (x_e cx))).
{ rewrite (RK (Z_to_bv 5 22)); [exact H22 | vm_compute; discriminate | apply wb10_notin; vm_compute; reflexivity]. }
assert (Hcell : forall o i, 0 <= o < 0x220 -> 0 <= i < 8 ->
  aview rsegs (w_H W2) (ms_mem ms) (q_R (x_e cx) + o + i) = aview rsegs (w_H W2) mem2 (q_R (x_e cx) + o + i)).
{ intros o i Ho Hi. apply HK. unfold T_SEG_STK, ASTACK in *. lia. }
rewrite (st_ok_restrict_mkst rsegs (w_H W2) _ _ ms HS eq_refl). cbn [ss_pc].
unfold rsb_from_C2 in HC2. apply (HC2 ly2 S2). unfold rsb_cut_C2.
split; [|split; [|split; [|split]]].
- apply (wb10_core_run B MT cx ly2 S2 W2 regs2 mem2 md2 (ms_regs ms) (ms_mem ms) _ (fun _ => False) HC HJ).
  + intros r Hr. apply RK; [destruct Hr as [->|[->| ->]]; vm_compute; discriminate |].
    apply wb10_notin. destruct Hr as [->|[->| ->]]; vm_compute; reflexivity.
  + apply same_io_wvb.
  + intros a Ha _. exact (HK a Ha).
  + intros a [].
- apply (wb10_L2_of_post cx (w_H W2) (ms_mem ms) (ms_regs ms)); [| exact R10 | exact R22 | lia].
  apply (rtmb_atl_kept rsegs (w_H W2) mem2 (w_H W2) (ms_mem ms) regs2 (ms_regs ms) (x_e cx) _ HL0).
  intros f Hf. unfold rsb_L_post, rsb_Hc in Hf. cbv zeta in Hf. cbn [app] in Hf.
  repeat (destruct Hf as [<-|Hf]; [cbn [fst rtmb_keeps rt_xv];
    first [ (apply RK; [vm_compute; discriminate | apply wb10_notin; vm_compute; reflexivity])
          | (intros i Hi; apply Hcell; lia) ] |]).
  destruct Hf.
- apply (rtmb_fsh_kept rsegs (w_H W2) mem2 (w_H W2) (ms_mem ms) (q_F (x_e cx)) rsb_P0 Hfsh).
  intros i Hi. apply HK. change (length rsb_P0) with 88%nat in Hi.
  pose proof (Z.div_pos (q_F (x_e cx)) 8 ltac:(lia)).
  assert (q_F (x_e cx) / 8 < 2 ^ 47) by (apply Z.div_lt_upper_bound; lia).
  unfold shadow_addr, SHADOW_OFF. lia.
- apply (rtmb_bytes_kept rsegs (w_H W2) mem2 (w_H W2) (ms_mem ms) (q_pp (x_e cx)) _ Hpp).
  intros x Hx. apply HK. rewrite (length_pp_bytes _ Hwf) in Hx. unfold PP_SIZE in Hx. lia.
- exact Hlen.
Qed.

(* ---- 0x82a14 -> 0x82a24: the shadow test of &pp->len (its address read from R+0x170) and the len load, then
   wb10_tail8 ---- *)
Lemma wb10_tail : forall (cx : rsb_scx rsegs) POST rest ly2 S2 (W2 : world rsegs) regs2 mem2 md2,
  rsb_pre rsegs B cx -> rsb_from_C2 rsegs B MT cx POST rest ->
  rsb_core rsegs B MT cx (rsb_E1 rsegs cx) ly2 S2 W2 regs2 mem2 md2 ->
  rsb_at_cx rsegs cx W2 mem2 regs2 (rsb_L_post rsegs cx) ->
  rsb_fsh_at rsegs cx W2 mem2 rsb_P0 ->
  rsb_pp_at rsegs cx W2 mem2 (pp_bytes (fst (pod_build rest))) -> q_len (x_e cx) = rt_len rest ->
  SRr rsegs W2 (cfg_at rsegs 0x82a14 regs2 mem2 md2) POST.
Proof.
intros cx POST rest ly2 S2 W2 regs2 mem2 md2 HP HC2 HC HL Hfsh Hpp Hlen.
pose proof wb10_wx as Hwx. pose proof wb10_segs_low as Hsegs.
pose proof (AR_laws_ok rsegs B) as LAWS.
destruct (wb10_ctx B MT cx ly2 S2 W2 regs2 mem2 md2 HP HC)
  as (Hin & Hfresh & Hal & Hlo & Hhi & Happ & Hpres & H2 & HR16 & HRS & HSTK & Hceil & H47 & HAR).
destruct (wb10_F_ctx B cx HP) as (HF1 & HF2 & HF3).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (wb10_rec_facts rest) as (Hwf & Hb & He & Hs).
pose proof (rt_len_bounds rest) as HLb.
set (L := rt_len rest) in *.
assert (HLv : val_mem rsegs (mrestrict (w_H W2) mem2) (q_pp (x_e cx) + 0x4000) 8 L).
{ exact (rtmb_pp_len rsegs (buf (fst (pod_build rest))) _ _ _ _ _ Hb He Hs (w_H W2) mem2 (q_pp (x_e cx)) Hpp). }
pose proof HL as HL0.
unfold rsb_at_cx, rsb_at, rsb_L_post, rsb_Hc in HL. cbv zeta in HL. cbn [app] in HL.
rewrite !Forall_cons_iff in HL.
destruct HL as (P8 & P9 & P19 & P20 & P7 & P24 & Q8 & Q10 & Q50 & Q60 & Qf8 & Q120 & Q138 & Q168 & Q170
  & Q48 & Q30 & Q38 & Q40 & Q18 & Q148 & _).
cbn [fst snd rt_at rt_xv] in P8, P9, P19, P20, P7, P24, Q170.
pose proof HC as (HJ & _).
remember (Ereg regs2 [Z_to_bv 64 L]) as E eqn:HE.
assert (E7 : ew E 7 = Z_to_bv 64 (q_pp (x_e cx) + 0x4000))
  by (subst E; rewrite (ew_Ereg_nat regs2 _ 7 (Z_to_bv 5 7) eq_refl); exact P7).
assert (E9 : ew E 9 = Z_to_bv 64 (q_R (x_e cx)))
  by (subst E; rewrite (ew_Ereg_nat regs2 _ 9 (Z_to_bv 5 9) eq_refl); exact P9).
assert (E20 : ew E 20 = Z_to_bv 64 SHADOW_OFF)
  by (subst E; rewrite (ew_Ereg_nat regs2 _ 20 (Z_to_bv 5 20) eq_refl); exact P20).
assert (E32 : ew E 32 = Z_to_bv 64 L) by (subst E; exact (ew_Ereg_extra regs2 _ 0)).
assert (Hsa : 0 <= shadow_addr (q_pp (x_e cx) + 0x4000) < 2 ^ 64).
{ pose proof (Z.div_pos (q_pp (x_e cx) + 0x4000) 8 ltac:(lia)).
  assert ((q_pp (x_e cx) + 0x4000) / 8 < 2 ^ 47) by (apply Z.div_lt_upper_bound; lia).
  unfold shadow_addr, SHADOW_OFF. lia. }
rewrite Z.mod_small in Q170 by exact Hsa.
assert (HRb : 4096 <= q_R (x_e cx) /\ q_R (x_e cx) + 0x220 <= 2 ^ 47) by (unfold T_SEG_STK, ASTACK in *; lia).
(* the cell R+0x170 lies above the first block *)
assert (HPD : pairwise_disjoint E
  [YP09.mkRegion (Some 9%nat) 0x170 0x178 0 0
     [YP09.mkChunk 0x170 (CVal 8 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 7 0) (SLit 3)) (SOff 20 0)))];
   YP09.mkRegion (Some 7%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 32 0))]]).
{ change (((bv_unsigned (ew E 9) + 0x178 <= bv_unsigned (ew E 7) + 0
            \/ bv_unsigned (ew E 7) + 8 <= bv_unsigned (ew E 9) + 0x170) /\ True) /\ (True /\ True)).
  rewrite E9, E7, !unsigned_lit_small by lia.
  split; [split; [right; unfold T_SEG_STK, ASTACK in *; lia | exact I] | split; exact I]. }
assert (HS : st_ok rsegs E (mkSS 0x82a14 sr_atoms
  [YP09.mkRegion (Some 9%nat) 0x170 0x178 0 0
     [YP09.mkChunk 0x170 (CVal 8 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 7 0) (SLit 3)) (SOff 20 0)))];
   YP09.mkRegion (Some 7%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 32 0))]] None
  (mkFacts [(7%nat, mkAF 4096 WB10_HI 4); (20%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (32%nat, mkAF 8 5440 0)] [] []))
  (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 0x82a14) mem2 (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. subst E. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor; [|constructor]].
    + apply (rtmb_ro_region rsegs _ (w_H W2) mem2 9 (q_R (x_e cx))).
      * rewrite E9. rewrite unsigned_lit_small by lia. reflexivity.
      * lia. * lia.
      * constructor; [|constructor].
        apply (chunk_ok_val rsegs _ _ (q_R (x_e cx)) 0x170 8 _ (shadow_addr (q_pp (x_e cx) + 0x4000))).
        -- exact (wb10_den_sh _ 7 20 (q_pp (x_e cx) + 0x4000) E7 ltac:(lia) E20).
        -- change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). exact Hsa.
        -- cbn. lia.
        -- exact Q170.
    + apply (rtmb_ro_region rsegs _ (w_H W2) mem2 7 (q_pp (x_e cx) + 0x4000)).
      * rewrite E7. rewrite unsigned_lit_small by lia. reflexivity.
      * lia. * lia.
      * constructor; [|constructor]. apply (chunk_ok_val rsegs _ _ (q_pp (x_e cx) + 0x4000) 0 8 (SOff 32 0) L).
        -- exact (wb10_den_atom _ 32 L E32). -- cbn. lia. -- cbn. lia. -- rewrite Z.add_0_r. exact HLv.
  - exact HPD.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E7, E20, E32, !unsigned_lit_small by (unfold SHADOW_OFF, WB10_HI; lia).
    repeat match goal with |- _ /\ _ => split end; try exact I; try (unfold SHADOW_OFF, WB10_HI; lia);
    try (rewrite Z.pow_0_r; apply Z.mod_1_r).
    change (2 ^ 4) with 16. rewrite Z.add_mod by lia. rewrite Hal. reflexivity. }
assert (SHOK : sh_ok rsegs WB10Bx [] E (mrestrict (w_H W2) mem2)) by constructor.
unfold cfg_at. change (w64 0x82a14) with (Z_to_bv 64 0x82a14).
aj_run_to_tok wb10_tbl_ok HS HJ SHOK WB10Bspan 0x82a24.
{ (* the shadow obligation of the 8-byte load of pp->len *)
  apply (wb10_ob_blk B ly2 S2 W2 mem2 md2 E (q_pp (x_e cx)) PP_SIZE (q_pp (x_e cx) + 0x4000) 8 (SOff 7 0) HAR Hin);
  [lia | change (req_size PP_SIZE) with 19744; lia
  | exact (wb10_U_atom E 20 SHADOW_OFF E20 ltac:(unfold SHADOW_OFF; lia))
  | exact (wb10_U_atom E 7 _ E7 ltac:(lia))]. }
{ awr_ok_tac. }
(* the run's end, at 0x82a24 *)
assert (HK : forall a, 0 <= a < 2 ^ 64 -> aview rsegs (w_H W2) (ms_mem ms) a = aview rsegs (w_H W2) mem2 a).
{ intros a Ha. apply (wb10_frame_kept _ _ _ _ _ HFr a Ha). intros (rg & Hr & Hrb). cbn [ss_mem] in Hr.
  destruct Hr as [<-|[<-|[]]]; cbn in Hrb; lia. }
assert (HAE : env_agree 32 (Ereg regs2 [Z_to_bv 64 L]) (ewset E 33 w))
  by (subst E; eapply env_agree_le; [|apply env_agree_ewset]; lia).
pose proof (regs_kept_of_st_ok rsegs _ _ ms regs2 [Z_to_bv 64 L] (w_H W2) [Z_to_bv 5 10; Z_to_bv 5 22]
  HS HAE ltac:(vm_compute; reflexivity)) as RK.
assert (R22 : getr (ms_regs ms) (Z_to_bv 5 22) = w64 (q_len (x_e cx))).
{ rewrite (st_ok_restrict_reg rsegs (w_H W2) _ _ ms (Z_to_bv 5 22) HS). wb10_sr_eval.
  rewrite (wb10_den_atom _ 32 L); [rewrite Hlen; reflexivity|]. rewrite ew_ewset_other by lia. exact E32. }
assert (Hcell : forall o i, 0 <= o < 0x220 -> 0 <= i < 8 ->
  aview rsegs (w_H W2) (ms_mem ms) (q_R (x_e cx) + o + i) = aview rsegs (w_H W2) mem2 (q_R (x_e cx) + o + i)).
{ intros o i Ho Hi. apply HK. unfold T_SEG_STK, ASTACK in *. lia. }
rewrite (st_ok_restrict_mkst rsegs (w_H W2) _ _ ms HS eq_refl). cbn [ss_pc].
apply (wb10_tail8 cx POST rest ly2 S2 W2 (ms_regs ms) (ms_mem ms) _ HP HC2).
- apply (wb10_core_run B MT cx ly2 S2 W2 regs2 mem2 md2 (ms_regs ms) (ms_mem ms) _ (fun _ => False) HC HJ).
  + intros r Hr. apply RK; [destruct Hr as [->|[->| ->]]; vm_compute; discriminate |].
    apply wb10_notin. destruct Hr as [->|[->| ->]]; vm_compute; reflexivity.
  + apply same_io_wvb.
  + intros a Ha _. exact (HK a Ha).
  + intros a [].
- apply (rtmb_atl_kept rsegs (w_H W2) mem2 (w_H W2) (ms_mem ms) regs2 (ms_regs ms) (x_e cx) _ HL0).
  intros f Hf. unfold rsb_L_post, rsb_Hc in Hf. cbv zeta in Hf. cbn [app] in Hf.
  repeat (destruct Hf as [<-|Hf]; [cbn [fst rtmb_keeps rt_xv];
    first [ (apply RK; [vm_compute; discriminate | apply wb10_notin; vm_compute; reflexivity])
          | (intros i Hi; apply Hcell; lia) ] |]).
  destruct Hf.
- exact R22.
- apply (rtmb_fsh_kept rsegs (w_H W2) mem2 (w_H W2) (ms_mem ms) (q_F (x_e cx)) rsb_P0 Hfsh).
  intros i Hi. apply HK. change (length rsb_P0) with 88%nat in Hi.
  pose proof (Z.div_pos (q_F (x_e cx)) 8 ltac:(lia)).
  assert (q_F (x_e cx) / 8 < 2 ^ 47) by (apply Z.div_lt_upper_bound; lia).
  unfold shadow_addr, SHADOW_OFF. lia.
- apply (rtmb_bytes_kept rsegs (w_H W2) mem2 (w_H W2) (ms_mem ms) (q_pp (x_e cx)) _ Hpp).
  intros x Hx. apply HK. rewrite (length_pp_bytes _ Hwf) in Hx. unfold PP_SIZE in Hx. lia.
- exact Hlen.
Qed.

(* ---- RT -> C2: corrupt = 1, then the tail ---- *)
Theorem wb10_req : rsb_piece_W10_req_stmt rsegs B MT.
Proof.
unfold rsb_piece_W10_req_stmt. intros cx POST rest Hst HC2.
unfold rsb_from_RT. intros ly2 S2 W2 regs2 mem2 md2 sh ps off bs r HRT.
destruct Hst as (HP & _).
destruct HRT as (HC & HL & Hfsh & Hpp & Hin & Hsuf & Hwf & Hlen & Htie & Hoff & Hob & Hb7).
pose proof wb10_wx as Hwx. pose proof wb10_segs_low as Hsegs.
pose proof (AR_laws_ok rsegs B) as LAWS.
destruct (wb10_ctx B MT cx ly2 S2 W2 regs2 mem2 md2 HP HC)
  as (Hinp & Hfresh & Hal & Hlo & Hhi & Happ & Hpres & H2 & HR16 & HRS & HSTK & Hceil & H47 & HAR).
destruct (wb10_F_ctx B cx HP) as (HF1 & HF2 & HF3).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (wb10_wf_facts sh ps Hwf) as (HW1 & HW2 & HW3 & HW4 & HW5).
unfold rsb_plen in Hob.
pose proof HL as HL0.
unfold rsb_at_cx, rsb_at, rsb_L_post, rsb_Hc in HL. cbv zeta in HL. cbn [app] in HL.
rewrite !Forall_cons_iff in HL.
destruct HL as (P8 & P9 & P19 & P20 & P7 & P24 & Q8 & Q10 & Q50 & Q60 & Qf8 & Q120 & Q138 & Q168 & Q170
  & Q48 & Q30 & Q38 & Q40 & Q18 & Q148 & _).
cbn [fst snd rt_at] in P8, P9, P19, P20, P7, P24.
pose proof HC as (HJ & _).
remember (Ereg regs2 []) as E eqn:HE.
assert (E20 : ew E 20 = Z_to_bv 64 SHADOW_OFF)
  by (subst E; rewrite (ew_Ereg_nat regs2 _ 20 (Z_to_bv 5 20) eq_refl); exact P20).
assert (E24 : ew E 24 = Z_to_bv 64 (q_pp (x_e cx) + 0x4d18))
  by (subst E; rewrite (ew_Ereg_nat regs2 _ 24 (Z_to_bv 5 24) eq_refl); exact P24).
assert (HS : st_ok rsegs E (mkSS 0x829fc sr_atoms
  [YP09.mkRegion (Some 24%nat) 0 4 0 4 []] None
  (mkFacts [(24%nat, mkAF 4096 WB10_HI 3); (20%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] []))
  (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 0x829fc) mem2 (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. subst E. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor].
    apply (rtmb_rw_region rsegs _ (w_H W2) mem2 24 (q_pp (x_e cx) + 0x4d18)).
    + rewrite E24. rewrite unsigned_lit_small by lia. reflexivity.
    + lia. + lia.
    + intros o Ho. apply Hpres. lia.
    + constructor.
  - cbn. tauto.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E20, E24, !unsigned_lit_small by (unfold SHADOW_OFF, WB10_HI; lia).
    repeat match goal with |- _ /\ _ => split end; try exact I; try (unfold SHADOW_OFF, WB10_HI; lia);
    try (rewrite Z.pow_0_r; apply Z.mod_1_r).
    change (2 ^ 3) with 8. rewrite Z.add_mod by lia.
    assert (Hm8 : q_pp (x_e cx) mod 8 = 0).
    { apply Z.mod_divide; [lia|]. apply Z.mod_divide in Hal; [|lia]. destruct Hal as [q Hq]. exists (2 * q). lia. }
    rewrite Hm8. reflexivity. }
(* the write window [pp + 0x4d18, + 4) is a shadow entry of the engine: its bytes are marked usable *)
assert (SHOK : sh_ok rsegs WB10Bx [mkSHE 24 0 4] E (mrestrict (w_H W2) mem2)).
{ constructor; [|constructor].
  apply (wb10_shent_blk B ly2 S2 W2 mem2 md2 E (q_pp (x_e cx)) PP_SIZE 24 0 4 HAR Hinp);
  change (req_size PP_SIZE) with 19744;
  [exact Happ | exact (wb10_U_atom E 20 SHADOW_OFF E20 ltac:(unfold SHADOW_OFF; lia)) | | | lia];
  rewrite (wb10_U_atom E 24 _ E24 ltac:(lia)); lia. }
unfold cfg_at. change (w64 RSB_RT) with (Z_to_bv 64 0x829fc).
aj_run_to_tok wb10_tbl_ok HS HJ SHOK WB10Bspan 0x82a14.
{ eapply (wb10_awr_cons_pp E _ _ _ _ _ _ _ _ _ 24%nat (q_pp (x_e cx) + 0x4d18) (q_pp (x_e cx)));
    [reflexivity | | exact Hinp | exact Hfresh | cbn; lia | cbn; unfold PP_SIZE; lia | apply awr_ok_nil].
  rewrite E24. apply unsigned_lit_small. lia. }
set (pc0 := q_pp (x_e cx) + 0x4d18) in *.
assert (HK : forall a, 0 <= a < 2 ^ 64 -> ~ (pc0 <= a < pc0 + 4) ->
  aview rsegs (w_H W2) (ms_mem ms) a = aview rsegs (w_H W2) mem2 a).
{ intros a Ha Hn. apply (wb10_frame_kept _ _ _ _ _ HFr a Ha). intros (rg & Hr & Hrb). cbn [ss_mem] in Hr.
  destruct Hr as [<-|[]]. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrb. rewrite E24 in Hrb.
  rewrite unsigned_lit_small in Hrb by lia. apply Hn. lia. }
assert (HV : val_mem rsegs (mrestrict (w_H W2) (ms_mem ms)) pc0 4 1).
{ pose proof (rtsb_region_nth _ _ ms 0 _ (w_H W2) HS eq_refl) as HR0.
  replace pc0 with (pc0 + 0) by lia.
  apply (wb10r_field _ _ 24 pc0 _ 0 4 0 4 0 4 (SLit 1) 1 HR0); [| left; reflexivity | reflexivity | cbn; lia | cbn; lia].
  rewrite !ew_ewset_other by lia. rewrite E24. apply unsigned_lit_small. lia. }
assert (HE0 : env_agree 32 (Ereg regs2 []) (ewset (ewset E 32 w) 33 w0)).
{ subst E. eapply env_agree_trans; [apply env_agree_ewset|]. eapply env_agree_le; [|apply env_agree_ewset]. lia. }
pose proof (regs_kept_of_st_ok rsegs _ _ ms regs2 [] (w_H W2) [Z_to_bv 5 10; Z_to_bv 5 11] HS HE0
  ltac:(vm_compute; reflexivity)) as RK.
assert (Hcell : forall o i, 0 <= o < 0x220 -> 0 <= i < 8 ->
  aview rsegs (w_H W2) (ms_mem ms) (q_R (x_e cx) + o + i) = aview rsegs (w_H W2) mem2 (q_R (x_e cx) + o + i)).
{ intros o i Ho Hi. apply HK; [unfold T_SEG_STK, ASTACK in *; lia|]. subst pc0. unfold T_SEG_STK, ASTACK in *. lia. }
assert (Himg : Z.of_nat (length (rsb_img_corr sh ps off bs (Z.of_nat (length bs)))) = PP_SIZE).
{ unfold rsb_img_corr. apply length_pp_image; [| exact HW3 | exact HW4].
  rewrite length_overwrite; [unfold POD_BUF_MAX; lia|]. rewrite length_firstn. lia. }
assert (Hnew : rsb_pp_at rsegs cx W2 (ms_mem ms) (pp_bytes (fst (pod_build rest)))).
{ rewrite Htie, <- (wb10_img_corrupt sh ps off bs Hwf ltac:(lia) ltac:(lia)).
  replace bs with (firstn (Z.to_nat (Z.of_nat (length bs))) bs) at 1 by (rewrite Nat2Z.id; apply firstn_all).
  fold (rsb_img_corr sh ps off bs (Z.of_nat (length bs))). unfold le32.
  apply (rtmb_bytes_store rsegs (w_H W2) mem2 (w_H W2) (ms_mem ms) (q_pp (x_e cx)) _ (Z.to_nat OFF_CORRUPT) 4 1 Hpp).
  - replace (q_pp (x_e cx) + Z.of_nat (Z.to_nat OFF_CORRUPT)) with pc0 by (subst pc0; unfold OFF_CORRUPT; lia).
    exact HV.
  - unfold OFF_CORRUPT, PP_SIZE in *. lia.
  - intros y Hy Hn. apply HK; [unfold PP_SIZE in *; lia|]. subst pc0. unfold OFF_CORRUPT in Hn. lia. }
rewrite (st_ok_restrict_mkst rsegs (w_H W2) _ _ ms HS eq_refl). cbn [ss_pc].
apply (wb10_tail cx POST rest ly2 S2 W2 (ms_regs ms) (ms_mem ms) _ HP HC2).
- apply (wb10_core_run B MT cx ly2 S2 W2 regs2 mem2 md2 (ms_regs ms) (ms_mem ms) _ (fun a => pc0 <= a < pc0 + 4) HC HJ).
  + intros rr Hr. apply RK; [destruct Hr as [->|[->| ->]]; vm_compute; discriminate |].
    apply wb10_notin. destruct Hr as [->|[->| ->]]; vm_compute; reflexivity.
  + apply same_io_wvb.
  + exact HK.
  + intros a Ha. right. subst pc0. unfold PP_SIZE. lia.
- apply (rtmb_atl_kept rsegs (w_H W2) mem2 (w_H W2) (ms_mem ms) regs2 (ms_regs ms) (x_e cx) _ HL0).
  intros f Hf. unfold rsb_L_post, rsb_Hc in Hf. cbv zeta in Hf. cbn [app] in Hf.
  repeat (destruct Hf as [<-|Hf]; [cbn [fst rtmb_keeps rt_xv];
    first [ (apply RK; [vm_compute; discriminate | apply wb10_notin; vm_compute; reflexivity])
          | (intros i Hi; apply Hcell; lia) ] |]).
  destruct Hf.
- apply (rtmb_fsh_kept rsegs (w_H W2) mem2 (w_H W2) (ms_mem ms) (q_F (x_e cx)) rsb_P0 Hfsh).
  intros i Hi. change (length rsb_P0) with 88%nat in Hi.
  pose proof (Z.div_pos (q_F (x_e cx)) 8 ltac:(lia)).
  assert (q_F (x_e cx) / 8 < 2 ^ 47) by (apply Z.div_lt_upper_bound; lia).
  apply HK; [unfold shadow_addr, SHADOW_OFF; lia|].
  pose proof (wb10_shadow_not_pp (q_pp (x_e cx)) (q_F (x_e cx)) i Happ HF3 ltac:(lia)) as Hsh.
  subst pc0. unfold PP_SIZE in Hsh. lia.
- exact Hnew.
- exact Hlen.
Qed.
End r.

Print Assumptions wb10_tail8.
Print Assumptions wb10_tail.
Print Assumptions wb10_req.
