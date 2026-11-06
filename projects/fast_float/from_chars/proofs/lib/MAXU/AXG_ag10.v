(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk SeqExec AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require Import MallocModel MallocInv.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AxMng MngHeap MngWb.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require MngHeap.
Import OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AxMng OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngHeap OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngWb OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngHeap.AxTry2.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AxBits MngZ MngNtfM AxTry AXG_as1 AXG_ag1 AXG_ag3p.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AXF_eez.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AXF_eez.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AXF_eez.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AXG_ag1.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AXF_taez.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AXF_taez.
Import OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AxBits OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.MngZ OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.MngNtfM OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AxTry OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXG_as1 OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXG_ag1 OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXG_ag3p OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_eez.AXF_nhdrz OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_eez.AXF_nzlz OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_eez.AXF_nfinz OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXG_ag1.AXF_ins1z OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_taez.AXF_ins2z OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_taez.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

(* [comment removed for export] *)
Fixpoint nzm (n : nat) (a size : Z) (m : word -> option byte) : word -> option byte :=
  match n with
  | O => m
  | S n' => nzm n' (a + size) size (wbytes m (wa a) (word_to_le_bytes 1 (wa 0)))
  end.

Lemma nzm_grows : forall n a size m, mem_grows m (nzm n a size m).
Proof.
  induction n as [|n IH]; intros a size m; cbn [nzm]; [apply mem_grows_refl|].
  exact (mem_grows_trans _ _ _ (wbytes_grows _ _ _) (IH _ _ _)).
Qed.

Lemma nzm_out : forall n a size m x, 0 <= x < 2^64 -> 0 <= a -> 1 <= size -> a + size * Z.of_nat n <= 2^64 ->
  (forall k, (k < n)%nat -> x <> a + size * Z.of_nat k) -> nzm n a size m (wa x) = m (wa x).
Proof.
  induction n as [|n IH]; intros a size m x Hx Ha Hs Hn Hk; cbn [nzm]; [reflexivity|].
  rewrite IH; [| exact Hx | lia | exact Hs | lia |].
  - assert (Ha' : a < 2^64) by lia.
    rewrite MngWb.wbytes_out; [reflexivity | cbn [length word_to_le_bytes Z_to_le_bytes]; rewrite u_wa_small by lia; lia | exact Hx |].
    rewrite u_wa_small by lia. specialize (Hk 0%nat ltac:(lia)). cbn [length word_to_le_bytes Z_to_le_bytes Z.of_nat] in *. lia.
  - intros k Hkn E. apply (Hk (S k) ltac:(lia)). rewrite E. lia.
Qed.

Lemma nzm_at : forall n a size m k, 0 <= a -> 1 <= size -> a + size * Z.of_nat n <= 2^64 -> (k < n)%nat ->
  nzm n a size m (wa (a + size * Z.of_nat k)) = Some (Z_to_bv 8 0).
Proof.
  induction n as [|n IH]; intros a size m k Ha Hs Hn Hk; [lia|]. cbn [nzm].
  destruct k as [|k].
  - rewrite Z.mul_0_r, Z.add_0_r. rewrite nzm_out; [| lia | lia | lia | lia |].
    + rewrite (MngWb.wbytes_at_wa0 (word_to_le_bytes 1 (wa 0)) m a) by (cbn [length word_to_le_bytes Z_to_le_bytes]; lia). reflexivity.
    + intros k Hk' E. nia.
  - replace (a + size * Z.of_nat (S k)) with ((a + size) + size * Z.of_nat k) by lia. apply IH; lia.
Qed.

Section AG10.
Context {fx : FPState}.

#[using="Type"] Theorem nz_loop : forall n R m rom a size, (1 <= n <= 33)%nat ->
  getr R 11 = wa (Z.of_nat n) -> getr R 12 = wa a -> getr R 24 = wa size -> 4096 <= a -> a + size * (Z.of_nat n - 1) <= 2^47 -> 16 <= size <= 2032 ->
  (forall k, (k < n)%nat -> forall d j, 0 <= d -> d + Z.of_nat j <= 1 -> store_ok SEGS m (wa (a + size * Z.of_nat k + 0 + d)) j = true) ->
  exists R', msteps SEGS (mkst R (wa 0x544e0) m rom) (mkst R' (wa 0x544f0) (nzm n a size m) rom) /\
    getr R' 11 = wa 0 /\ getr R' 12 = wa (a + size * Z.of_nat n) /\ getr R' 24 = wa size /\
    (forall k, In k [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 25; 26; 27; 28; 29; 30; 31]%nat ->
       getr R' (Z_to_bv 5 (Z.of_nat k)) = getr R (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  induction n as [|n IH]; intros R m rom a size Hn R11 R12 R24 Ha Han Hs W; [lia|].
  assert (P : nzl_pre R m (Z.of_nat (S n)) a size).
  { constructor; [exact R11 | exact R12 | exact R24 | lia | lia | lia |].
    intros d j Hd Hj. replace (a + 0 + d) with (a + size * Z.of_nat 0 + 0 + d) by lia. exact (W 0%nat ltac:(lia) d j Hd Hj). }
  destruct n as [|n'].
  - destruct (nzl_pnzx R m rom 1 a size P) as (R1 & Hms & A11 & A12 & A24 & AK).
    { scs_go; zats. reflexivity. }
    unfold nzl_mem_pnzx in Hms. rewrite Z.add_0_r in Hms. exists R1. split; [exact Hms|]. split; [rewrite A11; reflexivity|]. split; [rewrite A12; f_equal; lia|].
    split; [exact A24 | exact AK].
  - destruct (nzl_pnzc R m rom (Z.of_nat (S (S n'))) a size P) as (R1 & Hms & A11 & A12 & A24 & AK).
    { scs_go; zats. rewrite !Z.mod_small by lia. apply negb_true_iff. apply Z.eqb_neq. lia. }
    unfold nzl_mem_pnzc in Hms. rewrite Z.add_0_r in Hms.
    destruct (IH R1 (wbytes m (wa a) (word_to_le_bytes 1 (wa 0))) rom (a + size) size ltac:(lia)
                 ltac:(rewrite A11; f_equal; lia) A12 A24 ltac:(lia) ltac:(nia) Hs) as (R2 & Hms2 & B11 & B12 & B24 & BK).
    { intros k Hk d j Hd Hj. apply (store_ok_mono SEGS j m _ _ (wbytes_grows _ _ _)).
      replace (a + size + size * Z.of_nat k + 0 + d) with (a + size * Z.of_nat (S k) + 0 + d) by lia. exact (W (S k) ltac:(lia) d j Hd Hj). }
    exists R2. split; [exact (msteps_trans SEGS _ _ _ Hms Hms2)|]. split; [exact B11|]. split; [rewrite B12; f_equal; lia|].
    split; [exact B24|]. intros k Hk. rewrite (BK k Hk). apply AK. exact Hk.
Qed.
End AG10.

(* [comment removed for export] *)
Definition nt_hdr (m : word -> option byte) (mt p idx : Z) : word -> option byte :=
  wbytes (wbytes m (wa (mt + 32)) (word_to_le_bytes 8 (wa 0))) (wa (p + -3)) (word_to_le_bytes 1 (wa (idx + 192))).

Definition nt_ins1 (m : word -> option byte) (p mt sc cnt aidx usage hb : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes m (wa (8 * sc + 622184)) (word_to_le_bytes 8 (wa (cnt + usage))))
    (wa (mt + 24)) (word_to_le_bytes 4 (wa (2 ^ (aidx + 1) - 1)))) (wa (mt + 28)) (word_to_le_bytes 4 (wa ((2 ^ cnt - 1) - (2 ^ (aidx + 1) - 1)))))
    (wa (mt + 16)) (word_to_le_bytes 8 (wa p))) (wa (p + 0)) (word_to_le_bytes 8 (wa mt))) (wa (p + 8)) (word_to_le_bytes 1 (wa (aidx + 32 * Z.shiftr hb 5))))
    (wa (mt + 32)) (word_to_le_bytes 8 (wa (64 * sc + cnt + 31))).

Definition nt_mem (m : word -> option byte) (mt p sc cnt usage hb idx : Z) : word -> option byte :=
  mp_ins2 (nt_ins1 (nzm (Z.to_nat (cnt + 1)) (p + 12) (class_size sc) (nt_hdr m mt p idx)) p mt sc cnt (cnt - 1) usage hb) mt sc (cnt - 1).

Ltac side10 := cbn [length word_to_le_bytes Z_to_le_bytes]; (rewrite ?u_wa_small by lia); lia.

Section AG10T.
Context {fx : FPState}.

#[using="Type"] Theorem seg_ntail : forall R m rom sp0 sc req can ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 R0 mt p cnt usage hb idx,
  as_frame R0 m sp0 sc req can ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 ->
  getr R 2 = wa (sp0 + -144) -> getr R 8 = wa sc -> getr R 9 = wa mt -> getr R 10 = wa p -> getr R 19 = wa cnt ->
  getr R 20 = wa 621568 -> getr R 21 = wa (8 * sc + 621800) -> getr R 23 = wa (8 * sc + 621712) -> getr R 24 = wa (class_size sc) ->
  1 <= mt -> mt + 40 <= 0x10000 \/ 0x99000 <= mt -> mt mod 8 = 0 ->
  4096 <= p -> p mod 16 = 0 -> 1 <= cnt <= 32 -> 0 <= usage <= 2^60 -> 0 <= hb <= 255 -> 0 <= idx <= 31 ->
  p + 16 + class_size sc * cnt <= sp0 - 1024 -> (p + 16 + class_size sc * cnt <= 0x10000 \/ 0x99000 <= p - 4) ->
  (mt + 40 <= p - 4 \/ p + 16 + class_size sc * cnt <= mt) -> mt + 40 <= sp0 - 1024 -> class_size sc <= 2032 ->
  rdn SEGS m (wa (mt + 32)) 8 = Some (word_to_le_bytes 8 (wa 0)) ->
  rdn SEGS m (wa (mt + 0)) 8 = Some (word_to_le_bytes 8 (wa 0)) ->
  rdn SEGS m (wa (mt + 8)) 8 = Some (word_to_le_bytes 8 (wa 0)) ->
  rdn SEGS m (wa (p + -3)) 1 = Some (word_to_le_bytes 1 (wa idx)) ->
  rdn SEGS m (wa (8 * sc + 622184)) 8 = Some (word_to_le_bytes 8 (wa usage)) ->
  rdn SEGS m (wa (8 * sc + 621800)) 8 = Some (word_to_le_bytes 8 (wa 0)) ->
  rdn SEGS m (wa (p + 8)) 1 = Some (word_to_le_bytes 1 (wa hb)) ->
  (forall d k, 0 <= d -> d + Z.of_nat k <= 40 -> store_ok SEGS m (wa (mt + 0 + d)) k = true) ->
  (forall d k, 0 <= d -> d + Z.of_nat k <= 16 + class_size sc * cnt + 4 -> store_ok SEGS m (wa (p + -4 + d)) k = true) ->
  (forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (8 * sc + 622184 + d)) k = true) ->
  (forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (8 * sc + 621800 + d)) k = true) ->
  2^20 + 1024 <= sp0 ->
  exists R', msteps SEGS (mkst R (wa 0x544b8) m rom) (mkst R' (wa 0x54944) (nt_mem m mt p sc cnt usage hb idx) rom) /\
    getr R' 1 = wa ra /\ getr R' 2 = wa sp0 /\ getr R' 8 = wa s0 /\ getr R' 9 = wa s1 /\ getr R' 10 = wa 0 /\
    getr R' 18 = wa s2 /\ getr R' 19 = wa s3 /\ getr R' 20 = wa s4 /\ getr R' 21 = wa s5 /\ getr R' 22 = wa s6 /\
    getr R' 23 = wa s7 /\ getr R' 24 = wa s8 /\ getr R' 25 = wa s9 /\
    (forall k, In k [3; 4; 26; 27]%nat -> getr R' (Z_to_bv 5 (Z.of_nat k)) = getr R (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros R m rom sp0 sc req can ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 R0 mt p cnt usage hb idx F
    R2 R8 R9 R10 R19 R20 R21 R23 R24 Hmt Dmt Amt Hp Ap Hcnt Hu Hhb Hidx Sp Dp Dmp Smt Hsz
    Mw Mp Mn M3 Musg Mact Mhb Wmt Wp Wusg Wact Hsp'.
  pose proof F as [_ _ _ _ _ _ _ Hsp Asp Hsc Hreq Hcan Hra Hs0 Hs1 Hs2 Hs3 Hs4 Hs5 Hs6 Hs7 Hs8 Hs9
                   Fra Fs0 Fs1 Fs2 Fs3 Fs4 Fs5 Fs6 Fs7 Fs8 Fs9 Fcan Fgd].
  pose proof (size_classes_range sc ltac:(clear - Hsc; lia)) as Hun. pose proof (class_units sc) as Ecs.
  assert (Hsize : 16 <= class_size sc <= 2032) by (rewrite Ecs in *; clear - Hun Hsz; lia).
  set (size := class_size sc) in *.
  assert (Hend : p + 16 + size * cnt <= 2^47) by (clear - Sp Hsp; lia).
  assert (Hsc0 : 16 <= size * cnt <= 2032 * 32) by (clear - Hsize Hcnt; nia).
  (* [comment removed for export] *)
  assert (DA : forall x n, 0 <= n -> x + n <= 622648 -> 621568 <= x -> x + n <= mt \/ mt + 40 <= x) by (clear - Dmt; intros; lia).
  assert (DB : forall x n, 0 <= n -> x + n <= 622648 -> 621568 <= x -> x + n <= p - 4 \/ p + 16 + size * cnt <= x) by (clear - Dp; intros; lia).
  change (hide (mt + 40 <= 0x10000 \/ 0x99000 <= mt)) in Dmt. change (hide (p + 16 + size * cnt <= 0x10000 \/ 0x99000 <= p - 4)) in Dp.
  change (hide (mt + 40 <= p - 4 \/ p + 16 + size * cnt <= mt)) in Dmp.
  assert (DMP : mt + 40 <= p - 4 \/ p + 16 + size * cnt <= mt) by exact Dmp.
  (* [comment removed for export] *)
  assert (P1 : nhdr_pre R m p mt 0 idx cnt).
  { constructor; [exact R9 | exact R10 | exact R19 | clear - Hp Hend Hsc0; lia | clear - Hmt Smt Hsp; lia | clear; lia | clear - Hidx; lia | exact Hcnt
                 | exact Amt | exact Mw | exact M3 | | |].
    - intros d k Hd Hk. replace (mt + 32 + d) with (mt + 0 + (32 + d)) by ring. apply Wmt; clear - Hd Hk; lia.
    - intros d k Hd Hk. replace (p + -3 + d) with (p + -4 + (1 + d)) by ring. apply Wp; clear - Hd Hk Hsize Hcnt; nia.
    - clear - DMP Hsize Hcnt; nia. }
  destruct (nhdr_pnhdr R m rom p mt 0 idx cnt P1 ltac:(constructor)) as (R1 & Hms1 & A9 & A10 & A11 & A12 & A19 & AK). clear P1.
  assert (EM1 : nhdr_mem_pnhdr m R p mt 0 idx cnt = nt_hdr m mt p idx).
  { unfold nhdr_mem_pnhdr, nt_hdr. change ((Z.shiftr ((4503599627370496 * 0) mod 2^64) 52)) with 0.
    replace (Z.land idx 31) with idx by (change 31 with (Z.ones 5); rewrite Z.land_ones by lia; rewrite Z.mod_small by lia; reflexivity). reflexivity. }
  rewrite EM1 in Hms1. clear EM1. set (m1 := nt_hdr m mt p idx) in *.
  assert (G1 : mem_grows m m1) by (unfold m1, nt_hdr; do 2 (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl).
  assert (O1 : forall x, 0 <= x < 2^64 -> ~ (mt + 32 <= x < mt + 40) -> x <> p - 3 -> m1 (wa x) = m (wa x)).
  { intros x Hx N1 N2. unfold m1, nt_hdr. rewrite !MngWb.wbytes_out by (clear - Hx N1 N2 Hmt Smt Hsp Hp Hend Hsc0; side10). reflexivity. }
  (* [comment removed for export] *)
  assert (Hn : (1 <= Z.to_nat (cnt + 1) <= 33)%nat) by (clear - Hcnt; lia).
  destruct (nz_loop (Z.to_nat (cnt + 1)) R1 m1 rom (p + 12) size Hn ltac:(rewrite A11; f_equal; clear - Hcnt; lia) A12
              ltac:(regk AK 24%nat; exact R24) ltac:(clear - Hp; lia) ltac:(rewrite Z2Nat.id by lia; clear - Hend Hsize Hcnt Hsc0; nia) Hsize)
    as (R2' & Hms2 & B11 & B12 & B24 & BK).
  { intros k Hk d j Hd Hj. apply (store_ok_mono SEGS j m m1 _ G1).
    replace (p + 12 + size * Z.of_nat k + 0 + d) with (p + -4 + (16 + size * Z.of_nat k + d)) by ring. apply Wp; [clear - Hd Hsize; nia|].
    assert (Z.of_nat k <= cnt) by (clear - Hk Hcnt; lia). clear - Hd Hj H Hsize; nia. }
  set (m2 := nzm (Z.to_nat (cnt + 1)) (p + 12) size m1) in *.
  assert (G2 : mem_grows m1 m2) by apply nzm_grows.
  assert (O2 : forall x, 0 <= x < 2^64 -> (x < p + 12 \/ p + 13 + size * cnt <= x) -> m2 (wa x) = m1 (wa x)).
  { intros x Hx N. unfold m2. apply nzm_out; [exact Hx | clear - Hp; lia | clear - Hsize; lia | rewrite Z2Nat.id by lia; clear - Hend Hsize Hcnt; nia |].
    intros k Hk E. assert (Z.of_nat k < cnt + 1) by (clear - Hk Hcnt; lia). clear - N E H Hsize. nia. }
  assert (FR2 : forall x n, 0 <= x -> x + Z.of_nat n <= 2^64 -> (x + Z.of_nat n <= mt + 32 \/ mt + 40 <= x) ->
                   (x + Z.of_nat n <= p - 3 \/ p - 2 <= x) -> (x + Z.of_nat n <= p + 12 \/ p + 13 + size * cnt <= x) ->
                   rdn SEGS m2 (wa x) n = rdn SEGS m (wa x) n).
  { intros x n H1 H2 H3 H4 H5. apply rdn_frame_n; [exact H1 | exact H2 |]. intros y Hy.
    rewrite O2 by (clear - Hy H1 H2 H5; lia). apply O1; clear - Hy H1 H2 H3 H4; lia. }
  (* [comment removed for export] *)
  destruct (nfin_pnfin R2' m2 rom cnt ltac:(constructor; [regk BK 19%nat; exact A19 | exact Hcnt]) ltac:(constructor))
    as (R3 & Hms3 & C11 & C12 & C19 & C25 & CK).
  unfold nfin_mem_pnfin in Hms3.
  assert (P4 : ins1_pre R3 m2 p mt sc cnt (cnt - 1) usage 0 hb).
  { constructor.
    - regk CK 8%nat. regk BK 8%nat. regk AK 8%nat. exact R8.
    - regk CK 9%nat. regk BK 9%nat. exact A9.
    - regk CK 10%nat. regk BK 10%nat. exact A10.
    - exact C11.
    - rewrite C12. reflexivity.
    - regk CK 21%nat. regk BK 21%nat. regk AK 21%nat. exact R21.
    - regk CK 23%nat. regk BK 23%nat. regk AK 23%nat. exact R23.
    - exact C25.
    - clear - Hp Hend Hsc0; lia.
    - clear - Hmt Smt Hsp; lia.
    - exact Hsc.
    - exact Hcnt.
    - clear - Hcnt; lia.
    - exact Hu.
    - clear; lia.
    - exact Hhb.
    - exact Ap.
    - exact Amt.
    - rewrite FR2 by (pose proof (DA (8 * sc + 622184) 8); pose proof (DB (8 * sc + 622184) 8); clear - H H0 Hsc Hsize Hcnt; nia). exact Musg.
    - rewrite (rdn_frame_n (wbytes (wbytes m (wa (mt + 32)) (word_to_le_bytes 8 (wa 0))) (wa (p + -3)) (word_to_le_bytes 1 (wa (idx + 192))))
                 m2 (mt + 32) 8) by (first [clear - Hmt; lia | clear - Hmt Smt Hsp; lia | intros y Hy; rewrite O2 by (clear - Hy DMP Hmt Smt Hsp Hsize Hcnt; nia); reflexivity]).
      rewrite (rdn_frame_n (wbytes m (wa (mt + 32)) (word_to_le_bytes 8 (wa 0))) _ (mt + 32) 8) by
        (first [clear - Hmt; lia | clear - Hmt Smt Hsp; lia | intros y Hy; cbn [Z.of_nat Pos.of_succ_nat] in Hy; rewrite MngWb.wbytes_out by (clear - Hy DMP Hmt Smt Hsp Hp Hend Hsc0; side10); reflexivity]).
      apply rdn_wbytes_hit8. rewrite u_wa_small by (clear - Hmt Smt Hsp; lia). clear - Hmt Smt Hsp; lia.
    - rewrite FR2 by (clear - DMP Hp Hend Hsize Hcnt; cbn [Z.of_nat Pos.of_succ_nat]; nia). exact Mhb.
    - rewrite FR2 by (pose proof (DA (8 * sc + 621800) 8); pose proof (DB (8 * sc + 621800) 8); clear - H H0 Hsc Hsize Hcnt; nia). exact Mact.
    - rewrite FR2 by (clear - DMP Hmt Smt Hsp Hsize Hcnt; nia). exact Mp.
    - rewrite FR2 by (clear - DMP Hmt Smt Hsp Hsize Hcnt; nia). exact Mn.
    - intros d k Hd Hk. apply (store_ok_mono SEGS k m m2 _ (mem_grows_trans _ _ _ G1 G2)). exact (Wusg d k Hd Hk).
    - intros d k Hd Hk. apply (store_ok_mono SEGS k m m2 _ (mem_grows_trans _ _ _ G1 G2)). exact (Wmt d k Hd Hk).
    - intros d k Hd Hk. apply (store_ok_mono SEGS k m m2 _ (mem_grows_trans _ _ _ G1 G2)).
      replace (p + 0 + d) with (p + -4 + (4 + d)) by ring. apply Wp; clear - Hd Hk Hsize Hcnt; nia.
    - intros d k Hd Hk. apply (store_ok_mono SEGS k m m2 _ (mem_grows_trans _ _ _ G1 G2)). exact (Wact d k Hd Hk).
    - pose proof (DA (8 * sc + 622184) 8); clear - H Hsc; lia.
    - pose proof (DB (8 * sc + 622184) 8); clear - H Hsc Hsize Hcnt; nia.
    - clear - DMP Hsize Hcnt; nia.
    - pose proof (DA (8 * sc + 621800) 8); clear - H Hsc; lia.
    - pose proof (DB (8 * sc + 621800) 8); clear - H Hsc Hsize Hcnt; nia.
    - clear; lia. }
  destruct (ins1_pins1 R3 m2 rom p mt sc cnt (cnt - 1) usage 0 hb P4 ltac:(constructor)) as (R4 & Hms4 & D8 & D9 & D10 & D11 & D12 & D13 & D21 & D23 & D25 & DK).
  clear P4.
  assert (EM4 : ins1_mem_pins1 m2 R3 p mt sc cnt (cnt - 1) usage 0 hb = nt_ins1 m2 p mt sc cnt (cnt - 1) usage hb).
  { unfold ins1_mem_pins1, nt_ins1. change (Z.shiftr 0 12) with 0. rewrite Z.mul_0_r, !Z.add_0_r. reflexivity. }
  rewrite EM4 in Hms4. clear EM4. set (m3 := nt_ins1 m2 p mt sc cnt (cnt - 1) usage hb) in *.
  assert (G3 : mem_grows m2 m3) by (unfold m3, nt_ins1; do 7 (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl).
  (* [comment removed for export] *)
  assert (Hav : 1 <= 2 ^ (cnt - 1 + 1) - 1 <= 2^32-1).
  { replace (cnt - 1 + 1) with cnt by ring. assert (2 <= 2 ^ cnt) by (change 2 with (2^1) at 1; apply Z.pow_le_mono_r; clear - Hcnt; lia).
    assert (2 ^ cnt <= 2^32) by (apply Z.pow_le_mono_r; clear - Hcnt; lia). clear - H H0; lia. }
  assert (FR3 : forall x n, 0 <= x -> x + Z.of_nat n <= 2^64 -> (x + Z.of_nat n <= mt + 16 \/ mt + 40 <= x) ->
                   (x + Z.of_nat n <= 8 * sc + 622184 \/ 8 * sc + 622192 <= x) -> (x + Z.of_nat n <= p \/ p + 9 <= x) ->
                   rdn SEGS m3 (wa x) n = rdn SEGS m2 (wa x) n).
  { intros x n H1 H2 H3 H4 H5. apply rdn_frame_n; [exact H1 | exact H2 |]. intros y Hy. unfold m3, nt_ins1.
    rewrite !MngWb.wbytes_out by (clear - Hy H1 H2 H3 H4 H5 Hmt Smt Hsp Hsc Hp Hend Hsc0; side10). reflexivity. }
  assert (M3av : rdn SEGS m3 (wa (mt + 24)) 4 = Some (word_to_le_bytes 4 (wa (2 ^ (cnt - 1 + 1) - 1)))).
  { unfold m3, nt_ins1. rewrite (rdn_frame_n (wbytes (wbytes m2 (wa (8 * sc + 622184)) (word_to_le_bytes 8 (wa (cnt + usage))))
                                  (wa (mt + 24)) (word_to_le_bytes 4 (wa (2 ^ (cnt - 1 + 1) - 1)))) _ (mt + 24) 4) by
      (first [clear - Hmt; lia | clear - Hmt Smt Hsp; lia | intros y Hy; cbn [Z.of_nat Pos.of_succ_nat] in Hy;
              rewrite !MngWb.wbytes_out by (clear - Hy Hmt Smt Hsp DMP Hp Hend Hsc0; side10); reflexivity]).
    pose proof (rdn_wbytes_hit SEGS (word_to_le_bytes 4 (wa (2 ^ (cnt - 1 + 1) - 1))) (wbytes m2 (wa (8 * sc + 622184)) (word_to_le_bytes 8 (wa (cnt + usage))))
                  (wa (mt + 24))) as H. rewrite length_N_to_le_bytes in H. apply H. rewrite u_wa_small by (clear - Hmt Smt Hsp; lia). clear - Hmt Smt Hsp; lia. }
  assert (G23 : mem_grows m m3) by exact (mem_grows_trans _ _ _ (mem_grows_trans _ _ _ G1 G2) G3).
  assert (P5 : ins2_pre R4 m3 mt sc (2 ^ (cnt - 1 + 1) - 1)).
  { constructor.
    - exact D9.
    - exact D21.
    - clear - Hmt Smt Hsp; lia.
    - exact Hsc.
    - exact Hav.
    - exact Amt.
    - exact M3av.
    - rewrite FR3 by (pose proof (DA (8 * sc + 621800) 8); pose proof (DB (8 * sc + 621800) 8); clear - H H0 Hsc Hsize Hcnt Hsc0; lia).
      rewrite FR2 by (pose proof (DA (8 * sc + 621800) 8); pose proof (DB (8 * sc + 621800) 8); clear - H H0 Hsc Hsize Hcnt Hsc0; nia). exact Mact.
    - rewrite FR3 by (pose proof (DA (8 * sc + 622184) 8); clear - H DMP Hmt Smt Hsp Hsc Hsc0; lia).
      rewrite FR2 by (clear - DMP Hmt Smt Hsp Hsize Hcnt; nia). exact Mp.
    - rewrite FR3 by (pose proof (DA (8 * sc + 622184) 8); clear - H DMP Hmt Smt Hsp Hsc Hsc0; lia).
      rewrite FR2 by (clear - DMP Hmt Smt Hsp Hsize Hcnt; nia). exact Mn.
    - intros d k Hd Hk. apply (store_ok_mono SEGS k m m3 _ G23). exact (Wmt d k Hd Hk).
    - intros d k Hd Hk. apply (store_ok_mono SEGS k m m3 _ G23). exact (Wact d k Hd Hk).
    - pose proof (DA (8 * sc + 621800) 8); clear - H Hsc; lia. }
  destruct (ins2_pins2 R4 m3 rom mt sc (2 ^ (cnt - 1 + 1) - 1) P5 ltac:(constructor)) as (R5 & Hms5 & E9 & E10 & E21 & EK).
  clear P5.
  assert (EM5 : ins2_mem_pins2 m3 R4 mt sc (2 ^ (cnt - 1 + 1) - 1) = mp_ins2 m3 mt sc (cnt - 1)).
  { unfold ins2_mem_pins2, mp_ins2. rewrite le4_av. replace (2 ^ (cnt - 1 + 1) - 1 - 1) with (2 ^ (cnt - 1 + 1) - 2) by ring. reflexivity. }
  rewrite EM5 in Hms5. clear EM5.
  change (mp_ins2 m3 mt sc (cnt - 1)) with (nt_mem m mt p sc cnt usage hb idx) in Hms5.
  (* [comment removed for export] *)
  assert (OUTF : forall x, sp0 - 96 <= x < sp0 \/ 621568 <= x < 621576 -> nt_mem m mt p sc cnt usage hb idx (wa x) = m (wa x)).
  { intros x Hx. pose proof (DA 621568 8) as H1. pose proof (DB 621568 8) as H2.
    assert (Hx' : 0 <= x < 2^64) by (clear - Hx Hsp; lia).
    unfold nt_mem, mp_ins2. rewrite !MngWb.wbytes_out by (clear - Hx Hx' H1 H2 Hsc Hmt Smt Hsp Hp Hend Hsc0 Sp; side10).
    unfold nt_ins1. rewrite !MngWb.wbytes_out by (clear - Hx Hx' H1 H2 Hsc Hmt Smt Hsp Hp Hend Hsc0 Sp; side10).
    fold m2. rewrite O2 by (clear - Hx Hx' H2 Hsp Sp Hsc0 Hsize; lia). apply O1; clear - Hx Hx' H1 H2 Hsp Smt Sp Hsc0; lia. }
  assert (F' : as_frame R0 (nt_mem m mt p sc cnt usage hb idx) sp0 sc req can ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9).
  { apply (as_frame_mem R0 m); [exact F | intros x Hx; apply OUTF; left; exact Hx | intros x Hx; apply OUTF; right; exact Hx]. }
  assert (P6 : tae_pre R5 (nt_mem m mt p sc cnt usage hb idx) can ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 sp0).
  { destruct F' as [_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Gra Gs0 Gs1 Gs2 Gs3 Gs4 Gs5 Gs6 Gs7 Gs8 Gs9 Gcan Ggd].
    constructor; try assumption.
    - regk EK 2%nat. regk DK 2%nat. regk CK 2%nat. regk BK 2%nat. regk AK 2%nat. exact R2.
    - regk EK 20%nat. regk DK 20%nat. regk CK 20%nat. regk BK 20%nat. regk AK 20%nat. exact R20. }
  destruct (tae_ptae R5 _ rom can ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 sp0 P6 ltac:(constructor))
    as (Rf & Hms6 & Q1 & Q2 & Q8 & Q9 & _ & _ & Q18 & Q19 & Q20 & Q21 & Q22 & Q23 & Q24 & Q25 & QK).
  unfold tae_mem_ptae in Hms6. clear P6.
  exists Rf. split.
  { exact (msteps_trans SEGS _ _ _ Hms1 (msteps_trans SEGS _ _ _ Hms2 (msteps_trans SEGS _ _ _ Hms3
           (msteps_trans SEGS _ _ _ Hms4 (msteps_trans SEGS _ _ _ Hms5 Hms6))))). }
  split; [exact Q1|]. split; [exact Q2|]. split; [exact Q8|]. split; [exact Q9|].
  split; [regk QK 10%nat; exact E10|].
  split; [exact Q18|]. split; [exact Q19|]. split; [exact Q20|]. split; [exact Q21|]. split; [exact Q22|].
  split; [exact Q23|]. split; [exact Q24|]. split; [exact Q25|].
  intros k Hk. rewrite (QK k ltac:(clear - Hk; klist Hk)), (EK k ltac:(clear - Hk; klist Hk)), (DK k ltac:(clear - Hk; klist Hk)),
    (CK k ltac:(clear - Hk; klist Hk)), (BK k ltac:(clear - Hk; klist Hk)). apply AK. clear - Hk. klist Hk.
Qed.
End AG10T.

