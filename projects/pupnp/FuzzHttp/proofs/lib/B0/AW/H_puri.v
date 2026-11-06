(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac Image Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac CellConv.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAW Require Import Segs Shadow Contracts ATac IcptA0.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.T7A0 Require Import ShadowKit.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.AW Require Import HttpRepA AWKit H_parse_uric H_puri_seg1 H_puri_seg.
Import ListNotations.
Open Scope Z_scope.

Section S.
Context {HC : HasCeiling}.
Variable FI : fs_if.
Local Notation FSIV W := ((FSB FI, FSB FI + A0_FS_SIZE) :: (sh (FSB FI), sh (FSB FI) + A0_FS_SHSIZE) :: W)%Z.

Definition puri_WA (O : Z) : list ivl := [(O, O + 216); (ERRNO_A, ERRNO_A + 4)]%Z.

Definition parse_uri_post_A (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F_ : bvmap 5 word) (fc : bv 32)
    (U O : Z) (ustr slack : list byte) (canary : word) (lo : Z) (st : fsstate FI) (m0 : mem) : machine_state -> Prop :=
  fun ms' => exists (r : Z) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (st' : fsstate FI),
    ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F_ (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch ((lo, q) :: FSIV (puri_WA O))%Z m0 m' /\ wmono asegs m0 m' /\ mem_inv asegs m'
    /\ fkeep FI (puri_WA O) st m0 m' /\ fs_live FI st' = fs_live FI st /\ RFAKE FI st' m'
    /\ stk asegs m' lo q /\ asan_env asegs m'
    /\ (r = 1 \/ r = -108)
    /\ exists junk',
         rw_cells asegs m' O [CB 216 junk']
         /\ bytes_at asegs m' U (ustr ++ Z_to_bv 8 0 :: slack)
         /\ (exists ev, rw_cells asegs m' ERRNO_A [C4 ev])
         /\ rw_cells asegs m' got_sspA [C8 (wz ssp_guardA)] /\ rw_cells asegs m' ssp_guardA [C8 canary]
         /\ rw_cells asegs m' GOT_GIF_A [C8 (wz GIF_A)] /\ (exists gv, rw_cells asegs m' GIF_A [C4 gv]).

Definition parse_uri_stmt_A : Prop :=
  forall (U O ulen lo q : Z) (ustr slack junk : list byte) (canary : word) (st : fsstate FI)
         (ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F_ : bvmap 5 word) (fc : bv 32) (m0 : mem),

  alloc_ceiling <= lo -> lo <= q - PURI_DEPTH_A -> q mod 16 = 0 -> q < 2^63 -> stk asegs m0 lo q ->

  q <= 2^47 - 64 -> shz m0 (sh lo) (sh q) -> shr m0 (sh lo - sh lo mod 8) (sh q + 8) ->
  mem_inv asegs m0 -> asan_env asegs m0 -> RFAKE FI st m0 -> fs_call_ok FI st tp 1 ->
  FSENV FI m0 ->
  tp = Z_to_bv 64 6190512 ->

  O mod 8 = 0 -> 0x609000 <= O -> O + 216 <= alloc_ceiling -> lb (fs_live FI st) O 216 -> shw m0 O 216 ->
  rw_cells asegs m0 O [CB 216 junk] ->

  Z.of_nat (length ustr) = ulen -> 0 <= ulen < 2^31 -> (- (U + ulen + 1)) mod 8 <= Z.of_nat (length slack) ->
  0x609000 <= U -> U + ulen + 1 + Z.of_nat (length slack) <= alloc_ceiling ->
  (U + ulen + 1 + Z.of_nat (length slack) <= FSB FI \/ FSB FI + A0_FS_SIZE <= U) ->
  (U + ulen + 1 + Z.of_nat (length slack) <= 0x7fff7000 \/ 0x10007fff8000 <= U) ->
  shw m0 U (ulen + 1) -> bytes_at asegs m0 U (ustr ++ Z_to_bv 8 0 :: slack) ->

  shw m0 HTTPS_A 6 -> shw m0 GIF_A 4 -> shw m0 MARKTAB_A 10 -> shw m0 RESVTAB_A 13 ->

  (exists ev, rw_cells asegs m0 ERRNO_A [C4 ev]) ->
  rw_cells asegs m0 got_sspA [C8 (wz ssp_guardA)] -> rw_cells asegs m0 ssp_guardA [C8 canary] ->
  rw_cells asegs m0 GOT_GIF_A [C8 (wz GIF_A)] -> (exists gv, rw_cells asegs m0 GIF_A [C4 gv]) ->
  evt asegs (parse_uri_post_A ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc U O ustr slack canary lo st m0)
    (MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 U) (Z_to_bv 64 ulen) (Z_to_bv 64 O) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F_ (Z_to_bv 64 puri_entryA) fc None m0 (seg_rom asegs)).

Hypothesis IC : icpt_contracts.
Hypothesis STACK_MALLOC_3 : stack_malloc_stmt FI 3.
Hypothesis SET_SHADOW_F5 : set_shadow_f5_stmt.

#[using="IC STACK_MALLOC_3 SET_SHADOW_F5"] Theorem parse_uri_spec_A : parse_uri_stmt_A.
Proof.
  unfold parse_uri_stmt_A. intros until m0.
  intros CLO LO AL16 QHI ST Q47 SHZ SHR MI AE RF0 FCO FE0 TPV OAL OLO OHI OLB SHWO OUT ULEN ULR PAD UIMG UHI UFS UBAND SHWU TXT S1 S2 S3 S4 ERR SSPG SSPC GOTG GIFC.
  assert (AL16' : q = 16 * (q / 16)) by (clear - AL16; Z.div_mod_to_equations; lia).
  assert (OAL' : O = 8 * (O / 8)) by (clear - OAL; Z.div_mod_to_equations; lia).
  assert (PINV : pinvU U O ustr slack canary m0 junk).
  { split; [exact OUT|]. split; [exact TXT|]. split; [exact ERR|]. split; [exact SSPG|]. split; [exact SSPC|]. split; [exact GOTG| exact GIFC]. }
  eapply evt_mono.
  { exact (puri_evt FI IC STACK_MALLOC_3 SET_SHADOW_F5 U O ulen lo q (q / 16) (O / 8) ustr slack st ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 canary
             CLO LO AL16' QHI RF0 FCO FE0 Q47 SHZ SHR OAL' OLO OHI OLB SHWO ULEN ULR PAD UIMG UHI UFS UBAND SHWU S1 S2 S3 S4 TPV junk
             t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 ST MI AE PINV). }
  intros ms' H. exact H.
Qed.
End S.
