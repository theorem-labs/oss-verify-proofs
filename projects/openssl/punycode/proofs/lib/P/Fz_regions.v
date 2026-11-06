(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.openssl.punycode.lib.Common Require Import PropExec CatExec CatSim SeqExec StoreOk.
From OSSVerify.Proofs.openssl.punycode.lib.LibA Require Import FpLift WpEngine LibKit StrKit WpTac WpMem.
From OSSVerify.Proofs.openssl.punycode.lib.LibP Require Import PCode PImg PDecode PA2u PSpecs.
From OSSVerify.Proofs.openssl.punycode.lib.LibA Require KBridge.
From OSSVerify.Proofs.openssl.punycode.lib.Lib Require Import Exec MState Frame Image.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Ltac getr_both H :=
  lazymatch type of H with ?A = ?B => let a := eval cbv in A in let b := eval cbv in B in change (a = b) in H end.

(* [comment removed for export] *)
Theorem decode_evt : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) spz p n out q max,
  sp = W spz -> a0 = W p -> a1 = W n -> a2 = W out -> a3 = W q -> v_jalr ra 0 = ra ->
  0 <= n < 2 ^ 31 -> 0 <= p -> p + n < 2 ^ 63 -> rd_ok m p n ->
  0 <= max <= 512 -> cell PSEGS m q 4 (W max) ->
  0x30e000 <= spz - 144 -> spz < 2 ^ 63 -> wr_ok PSEGS m (spz - 144) 144 ->
  0x30e000 <= out -> out + 4 * max < 2 ^ 63 -> wr_ok PSEGS m out (4 * max) ->
  0x30e000 <= q -> q + 4 < 2 ^ 63 -> wr_ok PSEGS m q 4 ->
  (out + 4 * max <= spz - 144 \/ spz <= out) -> (q + 4 <= spz - 144 \/ spz <= q) ->
  evt psegs (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
       ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F ra fc None m' (seg_rom psegs)
       /\ unch m m' (dec_FP spz out q max) /\ mem_grows m m')
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (W 0x1e0688) fc None m (seg_rom psegs)).
Proof.
  intros until max. intros Esp E0 E1 E2 E3 Hret Hn Hp Hpn Hrd Hmax Hqc Hsp Hsp2 Hfr Hout Hout2 Hwout Hq Hq2 Hwq Hdj1 Hdj2.
  set (R0 := mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6).
  eapply evt_mono.
  - apply (KBridge.spec_evt psegs (seg_rom psegs) (W 0x1e0688) ra m
             (fun regs' M' => (forall r : reg, ~ In (ridx r) KSdec -> getr regs' r = getr R0 r)
               /\ (forall x, ~ dec_FP spz out q max x -> M' x = m x) /\ mem_grows m M')).
    destruct (decode_spec R0 F fc m (seg_rom psegs) ra spz p n out q max eq_refl Hret Esp E0 E1 E2 E3 Hn Hp Hpn Hrd Hmax Hqc
                Hsp Hsp2 Hfr Hout Hout2 Hwout Hq Hq2 Hwq Hdj1 Hdj2) as (regs' & M' & Hms & _ & Hk & HU & HG & _).
    exists regs', M'. split; [exact Hms|]. split; [exact Hk|]. split; [exact HU | exact HG].
  - intros ms' (y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y18 & y19 & y20
                & y21 & y22 & y23 & y24 & y25 & y26 & y27 & y28 & y29 & y30 & y31 & M' & -> & Hk & HU & HG).
    unfold R0 in Hk. KBridge.keep_getrs Hk.
    exists y5, y6, y7, y10, y11, y12, y13, y14, y15, y16, y17, y28, y29, y30, y31, M'.
    split; [reflexivity|]. split; [exact HU | exact HG].
Qed.

(* [comment removed for export] *)
Theorem a2u_evt : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) S b len N out sb (eb : word),
  sp = W (S - 2240) -> s0 = W S -> s3 = W b ->
  cell PSEGS m (S - 2216) 8 (W 0) -> cell PSEGS m (S - 2216 + 8) 8 (W out) -> cell PSEGS m (S - 2216 + 16) 8 (W 0) ->
  cell PSEGS m (S - 2216 + 24) 8 (W 0) -> cell PSEGS m (S - 2216 + 32) 8 (W 16) -> cell PSEGS m (S - 2216 + 40) 8 (W sb) ->
  cell PSEGS m (S - 2216 + 48) 1 eb -> (bv_unsigned eb mod 2 ^ 8) mod 2 = 0 -> 0 < sb < 2 ^ 64 ->
  0 <= len < 2 ^ 31 -> len < N -> 0 < b -> b + N < 2 ^ 63 -> rd_ok m b N ->
  m (W (b + len)) = Some (Z_to_bv 8 0) -> (b + len) / 8 * 8 + 8 <= b + N ->
  img_ok m 0x3a658 0x3a660 -> img_ok m 0x3a690 0x3a698 -> img_ok m 0x1e151 0x1e156 ->
  0x30e000 <= S - 2384 -> S < 2 ^ 63 ->
  wr_ok PSEGS m (S - 2384) 168 -> wr_ok PSEGS m (S - 2200) 16 -> wr_ok PSEGS m (S - 2160) 2048 ->
  0x30e000 <= out -> out + 16 < 2 ^ 63 -> wr_ok PSEGS m out 16 ->
  (out + 16 <= S - 2384 \/ S <= out) -> (b + N <= S - 2384 \/ S <= b) -> (b + N <= out \/ out + 16 <= b) ->
  evt psegs (fun ms' => exists (y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 : word)
                              (m' : word -> option byte),
       ms' = MS (mkR y1 sp gp tp y5 y6 y7 s0 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31)
                F (W 0x1e0c08) fc None m' (seg_rom psegs)
       /\ unch m m' (a2u_FP S out) /\ mem_grows m m')
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (W 0x1e0a18) fc None m (seg_rom psegs)).
Proof.
  intros until eb.
  intros E2 E8 E19 C0 C8 C16 C24 C32 C40 C48 Heb Hsb Hlen HlenN Hb HbN Hrd Hnul Hslack Hi1 Hi2 Hi3 HS HS2 Hw1 Hw2 Hw3
    Hout Hout2 Hwo Hdo Hdb Hdbo.
  set (R0 := mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6).
  eapply evt_mono.
  - apply (KBridge.spec_evt psegs (seg_rom psegs) (W 0x1e0a18) (W 0x1e0c08) m
             (fun regs' M' => getr regs' 2%bv = getr R0 2%bv /\ getr regs' 3%bv = getr R0 3%bv
               /\ getr regs' 4%bv = getr R0 4%bv /\ getr regs' 8%bv = getr R0 8%bv
               /\ (forall x, ~ a2u_FP S out x -> M' x = m x) /\ mem_grows m M')).
    exact (a2u_loop_spec R0 F fc m (seg_rom psegs) S b len N out sb eb E2 E8 E19 C0 C8 C16 C24 C32 C40 C48 Heb Hsb Hlen HlenN
             Hb HbN Hrd Hnul Hslack Hi1 Hi2 Hi3 HS HS2 Hw1 Hw2 Hw3 Hout Hout2 Hwo Hdo Hdb Hdbo).
  - intros ms' (y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y18 & y19 & y20
                & y21 & y22 & y23 & y24 & y25 & y26 & y27 & y28 & y29 & y30 & y31 & M' & -> & G2 & G3 & G4 & G8 & HU & HG).
    unfold R0 in G2, G3, G4, G8. getr_both G2. getr_both G3. getr_both G4. getr_both G8. subst y2 y3 y4 y8.
    exists y1, y5, y6, y7, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19, y20, y21, y22, y23, y24, y25, y26, y27, y28, y29, y30, y31, M'.
    split; [reflexivity|]. split; [exact HU | exact HG].
Qed.
