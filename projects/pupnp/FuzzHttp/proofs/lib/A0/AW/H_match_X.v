(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac Image Ceiling Arr.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs Shadow Contracts ATac IcptA0.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.T7A0 Require Import ShadowKit.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.AW Require Import HttpRepA AWKit AWAuto AWAuto2 FakeKit HObjK HObjF H_scanner_get_token H_vfm_A H_vfm_G H_vfm_X H_vfm_GX H_match_shell H_match_A.
Import ListNotations.
Open Scope Z_scope.

Notation FMT_CHUNK_A := 0x21a00%Z.

Section MX.
Context {HC : HasCeiling}.
Hypothesis IC : icpt_contracts.
Variable FI : fs_if.
Hypothesis STACK_MALLOC_0 : stack_malloc_stmt FI 0.
Hypothesis STACK_MALLOC_1 : stack_malloc_stmt FI 1.

#[using="Type"] Lemma low_mframe : forall st m0 m m' X cs, RFAKE FI st m0 -> X + Z.of_nat (cells_size cs) <= 0x609000 ->
  rw_cells asegs m X cs ->
  munch [(fs_F FI st 0, fs_F FI st 0 + 64); (sh (fs_F FI st 0), sh (fs_F FI st 0) + 8); (fs_FL FI st 0, fs_FL FI st 0 + 1)] m m' -> wmono asegs m m' ->
  rw_cells asegs m' X cs.
Proof.
  intros st m0 m m' X cs RF HX PC MU WM.
  destruct (new_frame_facts FI st 0 m0 (fs_F FI st 0) (sh (fs_F FI st 0)) (fs_FL FI st 0) RF ltac:(lia) eq_refl eq_refl eq_refl) as (FCLS & FLO & FHI & FAL & FLLO & FLHI & APART).
  pose proof (fsb_ok FI) as (B1 & _).
  eapply rw_cells_transport; [exact PC| exact MU| exact WM|]. cbn [disjoint_from]. unfold sh, SHADOW_OFF.
  split; [left; lia|]. split; [left; clear - HX FLO B1; Z.div_mod_to_equations; lia|]. split; [left; lia| exact I].
Qed.

#[using="IC STACK_MALLOC_0 STACK_MALLOC_1"] Theorem match_chunkA : forall (S MB A len cap cur0 P P2 lo q : Z) (bs : list byte) (st : fsstate FI) (pv pw1 pw2 ev canary : word)
    (ra gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F_ : bvmap 5 word) (fc : bv 32) (m : mem),
  vf_okA FI q lo S MB A len cap cur0 bs st [(P, P + 4); (P2, P2 + 16); (ERRNO_A, ERRNO_A + 4)] -> lo <= q - 16384 -> q <= 2^47 - 64 -> RFAKE FI st m -> fs_call_ok FI st tp 2 ->
  FSENV FI m ->
  stk asegs m lo q -> mem_inv asegs m -> asan_env asegs m ->
  rw_cells asegs m S [C8 (wz MB); C8 (wz cur0); C4 (wz 0)] -> rw_cells asegs m MB (mbuf_cells A len cap) -> bytes_at asegs m A bs ->
  shw m S 24 -> shw m MB 32 -> shw m A (len + 1) -> shw m SEPTAB_A 20 -> shw m FMT_CHUNK_A 7 ->
  shz m (sh lo) (sh q) -> shr m (sh lo - sh lo mod 8) (sh q + 8) ->
  rw_cells asegs m P [C4 pv] -> shw m P 4 -> P mod 4 = 0 -> 0x609000 <= P ->
  rw_cells asegs m P2 [C8 pw1; C8 pw2] -> shw m P2 16 -> P2 mod 8 = 0 ->
  (P + 4 <= P2 \/ P2 + 16 <= P) ->
  bv_unsigned tp = 0x5e6970 -> clow canary ev m -> shw m ERRNO_A 4 ->
  0x609000 <= A -> nth_error bs (Z.to_nat len) = Some (Z_to_bv 8 0) -> len + 1 <= 2^40 ->
  evt asegs (match_postXA FI [(P, P + 4); (P2, P2 + 16); (ERRNO_A, ERRNO_A + 4)] (X_chunkA cur0 P P2 canary) ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc st lo S MB len cur0 m)
      (MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 (wz S) (wz FMT_CHUNK_A) (wz P) (wz P2) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F_ (wz match_entry) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros VOK LO Q2 RF FCO FE ST MI AE SC MBC BUF SHS SHMB SHAN SHSEP SHFMT SHZ SHR PC1 SHP1 PAL1 PLO PC2 SHP2 PAL2 AP12 TPV CLOW SHE ALO NULT LENB.
  pose proof VOK as VOK'. destruct VOK' as (CLO & _ & AL16 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CUR0 & _ & _ & _ & WXL & _ & _).
  assert (LENL : len + 1 <= Z.of_nat (length bs)) by (assert (Z.to_nat len < length bs)%nat by (apply nth_error_Some; rewrite NULT; discriminate); lia).
  assert (SHA : 0 < len -> shw m A len) by (intros _; apply (shw_sub m A (len + 1)); [exact SHAN| lia| lia| lia]).
  destruct (cbounds FI q lo S MB A len cap cur0 bs st P P2 m VOK RF PLO) as (_ & _ & _ & _ & _ & LBP & LBP2 & _).
  destruct (match_q_facts q AL16) as [QV QVAL].
  eapply (match_wrapA FI STACK_MALLOC_0 [(P, P + 4); (P2, P2 + 16); (ERRNO_A, ERRNO_A + 4)] FMT_CHUNK_A (X_chunkA cur0 P P2 canary)); try eassumption.
  - intros mA mB r c (pv' & pa & pb & ev' & H1 & H2 & (E1 & E2 & E3) & HX) MU WM. exists pv', pa, pb, ev'.
    split; [exact (chunk_mframe FI st m mA mB P [C4 pv'] RF LBP H1 MU WM)|]. split; [exact (out_mframed FI st m P2 RF LBP2 mA mB pa pb H2 MU WM)|].
    split; [| exact HX]. unfold clow, A0_got_ssp, A0_ssp_guard in *.
    split; [| split]; (eapply (low_mframe st m mA mB); [exact RF| simpl_sizes; lia| eassumption| exact MU| exact WM]).
  - intros m1 t0' t1' t2' a3' a4' a5' a6' a7' s5' s6' s7' s8' s9' s10' s11' t3' t4' t5' t6' F_' fc' MU1 WM1 FK1 ST1 MI1 AE1 RF1 FCO1 FE1 LIVE1 VA.
    assert (LSUB : forall g, In g (fs_live FI st) -> In g (fs_live FI (fs_next FI st 0))) by (intros g Hg; rewrite LIVE1; right; exact Hg).
    destruct (mctx_move FI q lo S MB A len cap cur0 bs st _ FMT_CHUNK_A 7 m m1 VOK LO Q2 RF ltac:(lia) ltac:(lia) MU1 WM1 FK1 SC MBC BUF SHS SHMB SHA SHSEP SHFMT SHZ SHR)
      as (SC1 & MBC1 & BUF1 & SHS1 & SHMB1 & SHA1 & SHSEP1 & SHFMT1 & SHZv & SHZ1 & SHR1).
    destruct (c4_pro FI q lo S MB A len cap cur0 bs st P P2 m VOK RF PLO pv m1 PC1 SHP1 WM1 FK1) as [PC1' SHP1'].
    destruct (mout_move FI st m m1 P2 pw1 pw2 RF WM1 FK1 LBP2 PC2 SHP2) as [PC2' SHP2'].
    destruct (clow_pro FI q lo S MB A len cap cur0 bs st P P2 m canary VOK RF PLO ev m1 CLOW SHE SHAN LENL MU1 WM1) as (CLOW1 & SHE1 & SHAN1).
    split_chunk VA 1%nat GC1 VA2. split_chunk VA2 1%nat GC2 VArest. replace (q + -40) with (q + -48 + 8) in GC2 by lia.
    pose proof (vf_ok_move FI q lo S MB A len cap cur0 bs st _ _ VOK LO Q2 LSUB) as VOKv.
    eapply (vf_chunkA IC FI STACK_MALLOC_1 (match_q q) lo S MB A len cap cur0 bs (fs_next FI st 0) P P2 m1 canary VOKv RF1 PLO AP12 (q + -48) pv pw1 pw2 ev); try eassumption.
    + exact (mva_shw q lo m1 (q + -48) CLO LO AL16 Q2 SHZ1 SHR1 ltac:(lia) ltac:(lia) ltac:(clear - AL16; Z.div_mod_to_equations; lia)).
    + exact (mva_shw q lo m1 (q + -48 + 8) CLO LO AL16 Q2 SHZ1 SHR1 ltac:(lia) ltac:(lia) ltac:(clear - AL16; Z.div_mod_to_equations; lia)).
    + lia.
    + change (2^47) with 140737488355328 in *. lia.
    + clear - AL16. Z.div_mod_to_equations. lia.
Qed.

End MX.
