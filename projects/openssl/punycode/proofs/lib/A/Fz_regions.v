(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.openssl.punycode.lib.Common Require Import PropExec CatExec CatSim SeqExec StoreOk.
From OSSVerify.Proofs.openssl.punycode.lib.LibA Require Import FpLift WpEngine LibKit StrKit WpTac WpMem.
From OSSVerify.Proofs.openssl.punycode.lib.LibA Require Import ACode AShadow ARt AImg ACheck ADecode ARtIc AIface AWpacket AA2u AInit AStore ASpecs2 ASpecs3.
From OSSVerify.Proofs.openssl.punycode.lib.LibA Require AFakeStack KBridge.
From OSSVerify.Proofs.openssl.punycode.lib.Lib Require Import Exec MState Frame ImageA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Theorem decode_evt : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) spz p n out q max,
  sp = W spz -> a0 = W p -> a1 = W n -> a2 = W out -> a3 = W q ->
  rt_ok m ->
  0 <= n < 2 ^ 31 -> memrange p n -> addr_ok m p n -> rd_ok m p n ->
  0 <= max <= 512 -> cell ASEGS m q 4 (W max) ->
  A_IMG_END <= spz - 2400 /\ spz < 2 ^ 63 -> (spz <= SB \/ HIMEM_BEG <= spz - 2400) ->
  wr_ok ASEGS m (spz - 2400) 2400 ->
  A_IMG_END <= out -> memrange out (4 * max) -> addr_ok m out (4 * max) ->
  (0 < max -> shw_ok m out (4 * max)) -> wr_ok ASEGS m out (4 * max) ->
  A_IMG_END <= q -> memrange q 4 -> addr_ok m q 4 -> wr_ok ASEGS m q 4 ->
  (out + 4 * max <= spz - 2400 \/ spz <= out) -> (q + 4 <= spz - 2400 \/ spz <= q) ->
  evt asegs (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
       ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (v_jalr ra 0) fc None m' (seg_rom asegs)
       /\ (a0' = W 0 \/ a0' = W 1)
       /\ unch m m' (dec_FP spz out q max) /\ mem_grows m m')
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (W 0x407b38) fc None m (seg_rom asegs)).
Proof.
  intros until max. intros Esp E0 E1 E2 E3 Hrt Hn Hmp Hokp Hrd Hmax Hqc Hsp Hspz Hfr Hout Hmout Hokout Hshout Hwout
    Hq Hmq Hokq Hwq Hdj1 Hdj2.
  pose (Post := fun (pc' : word) (l' : regfile) (M' : mem) =>
     pc' = v_jalr ra 0
     /\ same_except KSdec
          (KBridge.lofR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) l'
     /\ (rget l' 10 = W 0 \/ rget l' 10 = W 1)
     /\ unch m M' (dec_FP spz out q max) /\ mem_grows m M').
  eapply evt_mono; [apply (KBridge.reach_evt asegs (seg_rom asegs) (W 0x407b38) m Post) |].
  - eapply (decode_cps (seg_rom asegs) Post m spz p n out q max); try eassumption; try reflexivity.
    intros l' M' Hl' Hse Ha0 Hw HU HG. apply reach_done. unfold Post. cbn [rget lget KBridge.lofR].
    repeat split; assumption.
  - intros ms' (pc' & l' & M' & Hl' & (-> & Hse & Ha0 & HU & HG) & ->).
    exists (rget l' 5), (rget l' 6), (rget l' 7), (rget l' 10), (rget l' 11),
           (rget l' 12), (rget l' 13), (rget l' 14), (rget l' 15), (rget l' 16),
           (rget l' 17), (rget l' 28), (rget l' 29), (rget l' 30), (rget l' 31), M'.
    split; [| split; [exact Ha0 | split; [exact HU | exact HG]]].
    KBridge.keep_regs Hse. reflexivity.
Qed.

(* [comment removed for export] *)
Theorem store0_evt : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) b n,
  s5 = W b -> s3 = W n -> s8 = W SB ->
  0 < b -> 0 <= n -> b + n + 1 < 2 ^ 63 ->
  acc1 m (b + n) -> wr_ok ASEGS m (b + n) 1 ->
  evt asegs (fun ms' => exists m' : word -> option byte,
       ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (W (b + n)) (W (bv_unsigned s7 + 144)) (W 16) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9
                     s10 s11 t3 t4 t5 t6) F (W 0x1f3294) fc None m' (seg_rom asegs)
       /\ cell ASEGS m' (b + n) 1 (W 0) /\ unch m m' (fun x => inr x (b + n) 1) /\ mem_grows m m')
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (W 0x1f3274) fc None m (seg_rom asegs)).
Proof.
  intros until n. intros E5 E3 E8 Hb Hn Hbn Hacc Hwr.
  eapply evt_mono.
  - apply (KBridge.spec_evt asegs (seg_rom asegs) (W 0x1f3274) (W 0x1f3294) m
             (fun regs' M' => (forall r : reg, ~ In (ridx r) [10; 11; 12]%nat -> getr regs' r = getr
                 (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) r)
               /\ getr regs' 10%bv = W (b + n) /\ getr regs' 11%bv = W (bv_unsigned s7 + 144) /\ getr regs' 12%bv = W 16
               /\ cell ASEGS M' (b + n) 1 (W 0) /\ (forall x, ~ inr x (b + n) 1 -> M' x = m x) /\ mem_grows m M')).
    exact (store0_spec (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F fc m (seg_rom asegs) b n E5 E3 E8 Hb Hn Hbn Hacc Hwr).
  - intros ms' (y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y18 & y19 & y20
                & y21 & y22 & y23 & y24 & y25 & y26 & y27 & y28 & y29 & y30 & y31 & M' & -> & Hk & G10 & G11 & G12 & Hc & HU & HG).
    KBridge.getr_leaf G10. KBridge.getr_leaf G11. KBridge.getr_leaf G12. subst y10 y11 y12.
    KBridge.keep_getrs Hk.
    exists M'. split; [reflexivity|]. split; [exact Hc|]. split; [exact HU | exact HG].
Qed.

(* [comment removed for export] *)
Theorem a2u_evt : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) fs T ctx thr h L FB6 b len N out sb (eb : word),
  sp = W L -> tp = W TP -> s1 = W L -> s2 = W SB -> s3 = W (sha FB6) -> s5 = W (FB6 + 2208) -> s9 = W b -> s10 = W FB6 ->
  0 <= len < 2 ^ 31 -> len < N -> 0 < b -> b + N < 2 ^ 63 -> rd_ok m b N ->
  m (W (b + len)) = Some (Z_to_bv 8 0) -> (b + len) / 8 * 8 + 8 <= b + N ->
  memrange b N -> addr_ok m b (len + 1) -> shw_ok m b (len + 1) ->
  cell ASEGS m (FB6 + 2208) 8 (W 0) -> cell ASEGS m (FB6 + 2208 + 8) 8 (W out) -> cell ASEGS m (FB6 + 2208 + 16) 8 (W 0) ->
  cell ASEGS m (FB6 + 2208 + 24) 8 (W 0) -> cell ASEGS m (FB6 + 2208 + 32) 8 (W 16) -> cell ASEGS m (FB6 + 2208 + 40) 8 (W sb) ->
  cell ASEGS m (FB6 + 2208 + 48) 1 eb -> (bv_unsigned eb mod 2 ^ 8) mod 2 = 0 -> 0 < sb < 2 ^ 64 ->
  rt_ok m -> ic_ok m -> AFakeStack.fsrt_ok m fs T ctx thr -> AFakeStack.fsrt_wf fs T ctx thr -> uar_on m ->
  cell ASEGS m 0x5a9bd8 8 (W 0x26e830) /\ cell ASEGS m 0x5a9be0 8 (W 0x26ea98) ->
  img_ok m 0xc7860 0xc7865 -> cell ASEGS m (sha XNA) 1 (W 5) -> shw_ok m XNA 4 ->
  fs_wf fs -> 0 <= h < 2 ^ 64 -> cell ASEGS m fs 8 (W h) -> zeros m (fs + 4096) 16384 -> ring_wr m fs ->
  FB6 mod 64 = 0 -> A_IMG_END <= FB6 -> (FB6 + 4096 <= SB \/ HIMEM_BEG <= FB6) -> FB6 + 4096 <= HIMEM_END ->
  zeros m (sha FB6 + 276) 7 -> zeros m (sha FB6 + 4) 256 -> rd_ok m (sha FB6) 296 -> wr_ok ASEGS m (sha FB6 + 288) 3 ->
  wr_ok ASEGS m (FB6 + 32) 2048 -> wr_ok ASEGS m (FB6 + 2224) 16 -> wr_ok ASEGS m (FB6 + 2304) 4 -> wr_ok ASEGS m (FB6 + 2320) 6 ->
  A_IMG_END <= out -> memrange out 16 -> addr_ok m out 16 -> shw_ok m out 16 -> wr_ok ASEGS m out 16 ->
  A_IMG_END <= L - 2400 -> L + 96 < 2 ^ 63 -> L mod 32 = 0 -> wr_ok ASEGS m (L - 2400) 2496 ->
  a2u_sep fs L FB6 out b N ->
  AFakeStack.fsrt_sep (L - 2400) 2496 fs T ctx thr -> dom3_sep T ctx thr FB6 2400 -> dom3_sep T ctx thr out 16 ->
  dom3_sep T ctx thr fs 1085440 -> dom3_sep T ctx thr SB (HIMEM_BEG - SB) ->
  evt asegs (fun ms' => exists (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s8' s9' s10' s11' t3' t4' t5' t6' : word)
                              (m' : word -> option byte) (h' : Z),
       ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4' s5 s6' s7' s8' s9' s10' s11' t3' t4'
                     t5' t6') F (W 0x408478) fc None m' (seg_rom asegs)
       /\ cell ASEGS m' (L + 16) 8 s11 /\ cell ASEGS m' (L + 24) 8 s10 /\ cell ASEGS m' (L + 32) 8 s4
       /\ 0 <= h' < 2 ^ 64 /\ cell ASEGS m' fs 8 (W h') /\ zeros m' (fs + 4096) 16384
       /\ unch m m' (a2u_FP fs L FB6 out) /\ mem_grows m m')
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (W 0x4081c4) fc None m (seg_rom asegs)).
Proof.
  intros until eb.
  intros E2 E4 E9 E18 E19 E21 E25 E26 Hlen HlenN Hb HbN Hrd Hnul Hslack Hbm Hbok Hbsw C0 C8 C16 C24 C32 C40 C48 Heb Hsb
    Hrt Hic Hfsrt Hwf Huar Hgot Hxn Hxs Hxw Hfs Hh Chint Hz Hrwr HF1 HF2 HF2b HF3 Z1 Z2 R6 W6 Wb Wp Wq Ws
    Ho1 Ho2 Ho3 Ho4 Ho5 HL1 HL2 HL3 HwL Hsep Hfsep D1 D2 D3 D4.
  set (R0 := mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6).
  eapply evt_mono.
  - apply (KBridge.spec_evt asegs (seg_rom asegs) (W 0x4081c4) (W 0x408478) m
             (fun regs' M' => exists h', (forall r : reg, ~ In (ridx r) KSL -> getr regs' r = getr R0 r)
               /\ cell ASEGS M' (L + 16) 8 (getr R0 27%bv) /\ cell ASEGS M' (L + 24) 8 (getr R0 26%bv)
               /\ cell ASEGS M' (L + 32) 8 (getr R0 20%bv)
               /\ 0 <= h' < 2 ^ 64 /\ cell ASEGS M' fs 8 (W h') /\ zeros M' (fs + 4096) 16384
               /\ (forall x, ~ a2u_FP fs L FB6 out x -> M' x = m x) /\ mem_grows m M')).
    destruct (a2u_loop_spec R0 F fc m (seg_rom asegs) fs T ctx thr h L FB6 b len N out sb eb E2 E4 E9 E18 E19 E21 E25 E26
                Hlen HlenN Hb HbN Hrd Hnul Hslack Hbm Hbok Hbsw C0 C8 C16 C24 C32 C40 C48 Heb Hsb
                Hrt Hic Hfsrt Hwf Huar Hgot Hxn Hxs Hxw Hfs Hh Chint Hz Hrwr HF1 HF2 HF2b HF3 Z1 Z2 R6 W6 Wb Wp Wq Ws
                Ho1 Ho2 Ho3 Ho4 Ho5 HL1 HL2 HL3 HwL Hsep Hfsep D1 D2 D3 D4) as (regs' & M' & h' & Hms & HP).
    exists regs', M'. split; [exact Hms|]. exists h'. exact HP.
  - intros ms' (y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y18 & y19 & y20
                & y21 & y22 & y23 & y24 & y25 & y26 & y27 & y28 & y29 & y30 & y31 & M' & -> & h' & Hk & Cs1 & Cs2 & Cs3 & Hh' & Ch' & Hz'
                & HU & HG).
    unfold R0 in Hk. KBridge.keep_getrs Hk.
    exists y1, y5, y6, y7, y10, y11, y12, y13, y14, y15, y16, y17, y20, y22, y23, y24, y25, y26, y27, y28, y29, y30, y31, M', h'.
    split; [reflexivity|]. split; [exact Cs1|]. split; [exact Cs2|]. split; [exact Cs3|]. split; [exact Hh'|].
    split; [exact Ch'|]. split; [exact Hz'|]. split; [exact HU | exact HG].
Qed.

(* [comment removed for export] *)
Definition wi_sv (sra ss0 ss1 ss2 ss3 ss4 ss5 ss6 ss7 ss8 ss9 ss10 ss11 : word) (r : nat) : word :=
  match r with
  | 1%nat => sra | 8%nat => ss0 | 9%nat => ss1 | 18%nat => ss2 | 19%nat => ss3 | 20%nat => ss4 | 21%nat => ss5 | 22%nat => ss6
  | 23%nat => ss7 | 24%nat => ss8 | 25%nat => ss9 | 26%nat => ss10 | 27%nat => ss11 | _ => W 0
  end.

Ltac in_slot := first [left; reflexivity | right; in_slot].


(* [comment removed for export] *)
Theorem wpinit_r1_evt : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) fs T ctx thr h pkt lb spv,
  sp = W spv -> tp = W TP -> a0 = W pkt -> a1 = W lb ->
  rt_ok m -> ic_ok m -> AFakeStack.fsrt_ok m fs T ctx thr -> AFakeStack.fsrt_wf fs T ctx thr -> uar_on m ->
  fs_wf fs -> 0 <= h < 2 ^ 64 -> cell ASEGS m fs 8 (W h) -> zeros m (fs + 4096) 16384 -> ring_wr m fs ->
  A_IMG_END <= spv - 336 -> spv < 2 ^ 63 -> spv mod 32 = 0 -> wr_ok ASEGS m (spv - 336) 336 ->
  (spv <= fs \/ fs + FS_SIZE <= spv - 336) -> (spv <= SB \/ HIMEM_BEG <= spv - 336) ->
  AFakeStack.fsrt_sep (spv - 336) 336 fs T ctx thr ->
  let k := h mod 16384 in let FB := fs + 36864 + 64 * k in
  let R0 := mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 in
  evt asegs (fun ms' => exists (ra' t0' t1' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
       ms' = MS (mkR ra' (W (spv - 128)) gp tp t0' t1' t2' (W spv) (W (spv - 128)) (W (pkt + 16)) (W 0) (W 16) a3' a4' a5' a6' a7'
                     (W FB) (W lb) (W pkt) s5 s6 (W (pkt + 16)) (W (sha FB)) (W FB) (W SB) s11 t3' t4' t5' t6')
                F (W 0x26d8a0) fc None m' (seg_rom asegs)
       /\ (forall off r, In (off, r) WI_SLOTS -> cell ASEGS m' (spv - 128 + off) 8 (wi_sv ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 r))
       /\ cell ASEGS m' fs 8 (W (h + 1)) /\ cell ASEGS m' (fs + 4096 + k) 1 (W 1)
       /\ zeros m' (fs + 4096) k /\ zeros m' (fs + 4096 + k + 1) (16383 - k)
       /\ cell ASEGS m' (FB + 56) 8 (W (fs + 4096 + k))
       /\ unch m m' (FP_r1 fs spv) /\ mem_grows m m')
    (MS R0 F (W 0x26d794) fc None m (seg_rom asegs)).
Proof.
  intros until spv.
  intros E2 E4 E10 E11 Hrt Hic Hfsrt Hwf Huar Hfs Hh Chint Hz Hrwr HS1 HS2 HS3 Hw Hs1 Hs2 Hfsep k FB R0.
  eapply evt_mono.
  - apply (KBridge.spec_evt asegs (seg_rom asegs) (W 0x26d794) (W 0x26d8a0) m
             (fun regs' M' => (forall r : reg, ~ In (ridx r) KS_r1 -> getr regs' r = getr R0 r)
    /\ getr regs' 2%bv = W (spv - 128) /\ getr regs' 8%bv = W spv /\ getr regs' 9%bv = W (spv - 128)
    /\ getr regs' 10%bv = W (pkt + 16) /\ getr regs' 11%bv = W 0 /\ getr regs' 12%bv = W 16
    /\ getr regs' 18%bv = W FB /\ getr regs' 19%bv = W lb /\ getr regs' 20%bv = W pkt /\ getr regs' 23%bv = W (pkt + 16)
    /\ getr regs' 24%bv = W (sha FB) /\ getr regs' 25%bv = W FB /\ getr regs' 26%bv = W SB
    /\ (forall off r, In (off, r) WI_SLOTS -> cell ASEGS M' (spv - 128 + off) 8 (getr R0 (Z_to_bv 5 (Z.of_nat r))))
    /\ cell ASEGS M' fs 8 (W (h + 1)) /\ cell ASEGS M' (fs + 4096 + k) 1 (W 1)
    /\ zeros M' (fs + 4096) k /\ zeros M' (fs + 4096 + k + 1) (16383 - k)
    /\ cell ASEGS M' (FB + 56) 8 (W (fs + 4096 + k))
    /\ (forall x, ~ FP_r1 fs spv x -> M' x = m x) /\ mem_grows m M')).
    exact (wpinit_r1_spec R0 F fc m (seg_rom asegs) fs T ctx thr h pkt lb spv E2 E4 E10 E11 Hrt Hic Hfsrt Hwf Huar Hfs Hh Chint Hz
             Hrwr HS1 HS2 HS3 Hw Hs1 Hs2 Hfsep).
  - intros ms' (y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y18 & y19 & y20
                & y21 & y22 & y23 & y24 & y25 & y26 & y27 & y28 & y29 & y30 & y31 & M' & -> & Hk & G2 & G8 & G9 & G10 & G11 & G12
                & G18 & G19 & G20 & G23 & G24 & G25 & G26 & Hsl & C1 & C2 & Z1 & Z2 & C3 & HU & HG).
    KBridge.getr_leaf G2. KBridge.getr_leaf G8. KBridge.getr_leaf G9. KBridge.getr_leaf G10. KBridge.getr_leaf G11.
    KBridge.getr_leaf G12. KBridge.getr_leaf G18. KBridge.getr_leaf G19. KBridge.getr_leaf G20. KBridge.getr_leaf G23.
    KBridge.getr_leaf G24. KBridge.getr_leaf G25. KBridge.getr_leaf G26.
    subst y2 y8 y9 y10 y11 y12 y18 y19 y20 y23 y24 y25 y26.
    unfold R0 in Hk. KBridge.keep_getrs Hk.
    exists y1, y5, y6, y7, y13, y14, y15, y16, y17, y28, y29, y30, y31, M'.
    split; [reflexivity|].
    split.
    { intros off r Hin. specialize (Hsl off r Hin). unfold WI_SLOTS in Hin.
      repeat (destruct Hin as [E|Hin];
              [ injection E as <- <-;
                match type of Hsl with context [Z_to_bv 5 (Z.of_nat ?k)] =>
                  let kz := eval cbv in (Z.of_nat k) in
                  replace (Z_to_bv 5 (Z.of_nat k)) with (Z_to_bv 5 kz) in Hsl by reflexivity end;
                exact Hsl |]).
      destruct Hin. }
    split; [exact C1|]. split; [exact C2|]. split; [exact Z1|]. split; [exact Z2|].
    split; [exact C3|]. split; [exact HU | exact HG].
Qed.

(* [comment removed for export] *)
Theorem wpinit_r2_evt : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) fs pkt spv k
    (sra ss0 ss1 ss2 ss3 ss4 ss5 ss6 ss7 ss8 ss9 ss10 ss11 : word),
  let FB := fs + 36864 + 64 * k in
  let sv := wi_sv sra ss0 ss1 ss2 ss3 ss4 ss5 ss6 ss7 ss8 ss9 ss10 ss11 in
  s0 = W spv -> s2 = W FB -> s3 = W 0 -> s4 = W pkt -> s8 = W (sha FB) -> s9 = W FB -> s10 = W SB ->
  v_jalr sra 0 = sra ->
  fs_wf fs -> 0 <= k < 16384 ->
  (forall off r, In (off, r) WI_SLOTS -> cell ASEGS m (spv - 128 + off) 8 (sv r)) ->
  cell ASEGS m (FB + 56) 8 (W (fs + 4096 + k)) ->
  zeros m (fs + 4096) k -> zeros m (fs + 4096 + k + 1) (16383 - k) -> zeros m (sha (pkt + 40)) 1 ->
  A_IMG_END <= pkt -> memrange pkt 56 -> pkt mod 8 = 0 ->
  wr_ok ASEGS m (pkt + 40) 8 -> wr_ok ASEGS m FB 8 -> wr_ok ASEGS m (sha FB) 8 -> wr_ok ASEGS m (fs + 4096 + k) 1 ->
  A_IMG_END <= spv - 128 -> spv < 2 ^ 63 ->
  (spv <= fs \/ fs + FS_SIZE <= spv - 128) -> (spv <= SB \/ HIMEM_BEG <= spv - 128) ->
  (spv <= pkt \/ pkt + 56 <= spv - 128) -> (pkt + 56 <= fs \/ fs + 1085440 <= pkt) ->
  evt asegs (fun ms' => exists (a1' : word) (m' : word -> option byte) (a0v : Z),
       ms' = MS (mkR sra (W spv) gp tp t0 t1 t2 ss0 ss1 (W a0v) a1' a2 a3 a4 a5 a6 a7 ss2 ss3 ss4 ss5 ss6 ss7 ss8 ss9 ss10 ss11
                     t3 t4 t5 t6) F sra fc None m' (seg_rom asegs)
       /\ (bv_unsigned a0 = 0 -> a0v = 0) /\ (bv_unsigned a0 <> 0 -> a0v = 1)
       /\ cell ASEGS m' (pkt + 40) 8 a0 /\ zeros m' (fs + 4096) 16384
       /\ unch m m' (FP_r2 fs pkt k) /\ mem_grows m m')
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (W 0x26d8b8) fc None m (seg_rom asegs)).
Proof.
  intros until ss11. intros FB sv.
  intros E8 E18 E19 E20 E24 E25 E26 Hret Hfs Hk Hsaved C56 Z1 Z2 Zp Hp1 Hp2 Hp3 W1 W2 W3 W4 HS1 HS2 Hs1 Hs2 Hs3 Hs4.
  set (R0 := mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6).
  eapply evt_mono.
  - apply (KBridge.spec_evt asegs (seg_rom asegs) (W 0x26d8b8) sra m
             (fun regs' M' => exists a0v, (forall r : reg, ~ In (ridx r) KS_r2 -> getr regs' r = getr R0 r)
    /\ getr regs' 2%bv = W spv /\ getr regs' 10%bv = W a0v
    /\ (bv_unsigned a0 = 0 -> a0v = 0) /\ (bv_unsigned a0 <> 0 -> a0v = 1)
    /\ (forall off r, In (off, r) WI_SLOTS -> getr regs' (Z_to_bv 5 (Z.of_nat r)) = sv r)
    /\ cell ASEGS M' (pkt + 40) 8 a0 /\ zeros M' (fs + 4096) 16384
    /\ (forall x, ~ FP_r2 fs pkt k x -> M' x = m x) /\ mem_grows m M')).
    destruct (wpinit_r2_spec R0 F fc m (seg_rom asegs) fs pkt spv k a0 sv E8 eq_refl E18 E19 E20 E24 E25 E26 Hret Hfs Hk Hsaved
                C56 Z1 Z2 Zp Hp1 Hp2 Hp3 W1 W2 W3 W4 HS1 HS2 Hs1 Hs2 Hs3 Hs4) as (regs' & M' & a0v & Hms & HP).
    exists regs', M'. split; [exact Hms|]. exists a0v. exact HP.
  - intros ms' (y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y18 & y19 & y20
                & y21 & y22 & y23 & y24 & y25 & y26 & y27 & y28 & y29 & y30 & y31 & M' & -> & a0v & Hk' & G2 & G10 & Ha1 & Ha2 & Hrs
                & Cp & Zr & HU & HG).
    KBridge.getr_leaf G2. KBridge.getr_leaf G10. subst y2 y10.
    pose proof (Hrs 120 1%nat ltac:(unfold WI_SLOTS; in_slot)) as R1. pose proof (Hrs 112 8%nat ltac:(unfold WI_SLOTS; in_slot)) as R8.
    pose proof (Hrs 104 9%nat ltac:(unfold WI_SLOTS; in_slot)) as R9. pose proof (Hrs 96 18%nat ltac:(unfold WI_SLOTS; in_slot)) as R18.
    pose proof (Hrs 88 19%nat ltac:(unfold WI_SLOTS; in_slot)) as R19. pose proof (Hrs 80 20%nat ltac:(unfold WI_SLOTS; in_slot)) as R20.
    pose proof (Hrs 72 21%nat ltac:(unfold WI_SLOTS; in_slot)) as R21. pose proof (Hrs 64 22%nat ltac:(unfold WI_SLOTS; in_slot)) as R22.
    pose proof (Hrs 56 23%nat ltac:(unfold WI_SLOTS; in_slot)) as R23. pose proof (Hrs 48 24%nat ltac:(unfold WI_SLOTS; in_slot)) as R24.
    pose proof (Hrs 40 25%nat ltac:(unfold WI_SLOTS; in_slot)) as R25. pose proof (Hrs 32 26%nat ltac:(unfold WI_SLOTS; in_slot)) as R26.
    pose proof (Hrs 24 27%nat ltac:(unfold WI_SLOTS; in_slot)) as R27. clear Hrs.
    replace (Z_to_bv 5 (Z.of_nat 1)) with (1%bv : reg) in R1 by (apply bv_eq; reflexivity).
    replace (Z_to_bv 5 (Z.of_nat 8)) with (8%bv : reg) in R8 by (apply bv_eq; reflexivity).
    replace (Z_to_bv 5 (Z.of_nat 9)) with (9%bv : reg) in R9 by (apply bv_eq; reflexivity).
    replace (Z_to_bv 5 (Z.of_nat 18)) with (18%bv : reg) in R18 by (apply bv_eq; reflexivity).
    replace (Z_to_bv 5 (Z.of_nat 19)) with (19%bv : reg) in R19 by (apply bv_eq; reflexivity).
    replace (Z_to_bv 5 (Z.of_nat 20)) with (20%bv : reg) in R20 by (apply bv_eq; reflexivity).
    replace (Z_to_bv 5 (Z.of_nat 21)) with (21%bv : reg) in R21 by (apply bv_eq; reflexivity).
    replace (Z_to_bv 5 (Z.of_nat 22)) with (22%bv : reg) in R22 by (apply bv_eq; reflexivity).
    replace (Z_to_bv 5 (Z.of_nat 23)) with (23%bv : reg) in R23 by (apply bv_eq; reflexivity).
    replace (Z_to_bv 5 (Z.of_nat 24)) with (24%bv : reg) in R24 by (apply bv_eq; reflexivity).
    replace (Z_to_bv 5 (Z.of_nat 25)) with (25%bv : reg) in R25 by (apply bv_eq; reflexivity).
    replace (Z_to_bv 5 (Z.of_nat 26)) with (26%bv : reg) in R26 by (apply bv_eq; reflexivity).
    replace (Z_to_bv 5 (Z.of_nat 27)) with (27%bv : reg) in R27 by (apply bv_eq; reflexivity).
    unfold sv in R1, R8, R9, R18, R19, R20, R21, R22, R23, R24, R25, R26, R27.
    cbn [wi_sv] in R1, R8, R9, R18, R19, R20, R21, R22, R23, R24, R25, R26, R27.
    KBridge.getr_leaf R1. KBridge.getr_leaf R8. KBridge.getr_leaf R9. KBridge.getr_leaf R18. KBridge.getr_leaf R19.
    KBridge.getr_leaf R20. KBridge.getr_leaf R21. KBridge.getr_leaf R22. KBridge.getr_leaf R23. KBridge.getr_leaf R24.
    KBridge.getr_leaf R25. KBridge.getr_leaf R26. KBridge.getr_leaf R27.
    subst y1 y8 y9 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27.
    unfold R0 in Hk'. KBridge.keep_getrs Hk'.
    exists y11, M', a0v.
    split; [reflexivity|]. split; [exact Ha1|]. split; [exact Ha2|]. split; [exact Cp|]. split; [exact Zr|].
    split; [exact HU | exact HG].
Qed.
