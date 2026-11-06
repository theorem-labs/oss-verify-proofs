(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3 SeqExec.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocModel MallocInv MallocLemmasBase.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr MallocWfMeta.
Import OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocModel OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocLemmasBase OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocLemmasRing OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfFrame OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr.MallocWfGeom OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng MngRepr MngHeap MngImage MngWb MngWk MngGeoX MngLt MngSurgery MngExc MngNtfPre MngNtfC MngGM MngCtx2.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AxBits MngZ MngNtfM MngNtfS MngMWP MngMW0 MngMW1 MngMW2 MngShift.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AXF_eez.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AXF_mmwz.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AXF_eez.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AXF_mcp0z.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AXF_mmwz.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AXF_eez.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AXF_eez.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AXG_am1 AXG_am3 AXG_am4 AXG_am5 AXG_am6 AXG_am7 AXG_am6b AXG_amr0 AXG_amr AXG_am6c AXG_am6d AXG_am6e MngL4.
Import OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AxBits OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.MngZ OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.MngNtfM OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.MngNtfS OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.MngMWP OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.MngMW0 OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.MngMW1 OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.MngMW2 OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.MngShift OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_eez.AXF_mi0z OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_mmwz.AXF_mil2z OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_eez.AXF_mirz OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_mcp0z OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_mmwz.AXF_mic2z OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_eez.AXF_mixz OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_eez.AXF_mt2z OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXG_am1 OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXG_am3 OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXG_am4 OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXG_am5 OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXG_am6 OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXG_am7 OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXG_am6b OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXG_amr0 OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXG_amr OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXG_am6c OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXG_am6d OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXG_am6e OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.MngL4.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma Z_to_le_bytes_add : forall n k z, Z_to_le_bytes (n + k) z = Z_to_le_bytes n z ++ Z_to_le_bytes k (Z.shiftr z (8 * Z.of_nat n)).
Proof.
  induction n as [|n IH]; intros k z.
  - cbn [Nat.add Z_to_le_bytes app]. rewrite Z.shiftr_0_r. reflexivity.
  - cbn [Nat.add Z_to_le_bytes app]. f_equal. rewrite IH. f_equal. rewrite Z.shiftr_shiftr by lia. do 2 f_equal. lia.
Qed.

(* [comment removed for export] *)
Lemma le8_split : forall w, 0 <= w < 2^64 ->
  word_to_le_bytes 4 (wa (ext_Z true 0 4 w)) ++ word_to_le_bytes 4 (wa (Z.shiftr w 32)) = word_to_le_bytes 8 (wa w).
Proof.
  intros w Hw. unfold word_to_le_bytes. rewrite !u_wa. change 8%nat with (4 + 4)%nat. rewrite Z_to_le_bytes_add.
  f_equal.
  - apply Z_to_le_bytes_eqm. change (8 * Z.of_nat 4) with 32. rewrite !Z.mod_mod_divide by (first [(exists (2^32); reflexivity) | lia]).
    unfold ext_Z. cbn [Z.of_nat N.of_nat]. change (2 ^ (8 * 0)) with 1. change (2 ^ (8 * 4)) with (2^32). change (8 * N.pos 4)%N with 32%N.
    rewrite Z.div_1_r. rewrite swrap32_mod, Z.mod_mod by lia. reflexivity.
  - apply Z_to_le_bytes_eqm. change (8 * Z.of_nat 4) with 32. rewrite (Z.mod_small w) by lia.
    rewrite (Z.mod_small (Z.shiftr w 32)); [reflexivity|]. rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia|].
    apply Z.div_lt_upper_bound; lia.
Qed.

Lemma wbytes_app_pt : forall bs1 bs2 (m : word -> option byte) a x, 0 <= a -> a + Z.of_nat (length bs1) + Z.of_nat (length bs2) < 2^64 ->
  0 <= x < 2^64 ->
  wbytes (wbytes m (wa a) bs1) (wa (a + Z.of_nat (length bs1))) bs2 (wa x) = wbytes m (wa a) (bs1 ++ bs2) (wa x).
Proof.
  intros bs1 bs2 m a x Ha Hl Hx.
  destruct (Z_lt_le_dec x a) as [D|D]; [rewrite !MngWb.wbytes_out by (first [side | (rewrite ?length_app; rewrite ?u_wa_small by lia; lia)]); reflexivity|].
  destruct (Z_lt_le_dec x (a + Z.of_nat (length bs1))) as [D2|D2].
  - rewrite MngWb.wbytes_out by (rewrite ?u_wa_small by lia; lia).
    replace x with (a + Z.of_nat (Z.to_nat (x - a))) by lia.
    rewrite !MngWb.wbytes_at_wa by (rewrite ?length_app; lia). rewrite app_nth1 by lia. reflexivity.
  - destruct (Z_lt_le_dec x (a + Z.of_nat (length bs1) + Z.of_nat (length bs2))) as [D3|D3].
    + replace x with (a + Z.of_nat (length bs1) + Z.of_nat (Z.to_nat (x - a - Z.of_nat (length bs1)))) by lia.
      rewrite MngWb.wbytes_at_wa by lia.
      replace (a + Z.of_nat (length bs1) + Z.of_nat (Z.to_nat (x - a - Z.of_nat (length bs1))))
        with (a + Z.of_nat (length bs1 + Z.to_nat (x - a - Z.of_nat (length bs1)))) by lia.
      rewrite MngWb.wbytes_at_wa by (rewrite ?length_app; lia). rewrite app_nth2 by lia. f_equal. f_equal. lia.
    + rewrite !MngWb.wbytes_out by (first [side | (rewrite ?length_app; rewrite ?u_wa_small by lia; lia)]). reflexivity.
Qed.

Lemma mcp0_pt : forall (m : word -> option byte) (R : bvmap 5 word) dst q w x, 0 <= dst -> dst + 8 < 2^64 -> 0 <= w < 2^64 -> 0 <= x < 2^64 ->
  mcp0_mem_pmcp0 m R dst q w (wa x) = wbytes m (wa dst) (word_to_le_bytes 8 (wa w)) (wa x).
Proof.
  intros m R dst q w x H0 H1 Hw Hx. unfold mcp0_mem_pmcp0. rewrite Z.add_0_r.
  rewrite <- (le8_split w Hw). rewrite <- wbytes_app_pt by (cbn [length word_to_le_bytes Z_to_le_bytes]; lia).
  reflexivity.
Qed.

Lemma existsb_firstn_S : forall (l : list Z) i, (i < length l)%nat ->
  existsb (Z.eqb 25) (firstn (S i) l) = existsb (Z.eqb 25) (firstn i l) || (nth i l 0 =? 25).
Proof.
  induction l as [|a t IH]; intros i Hi; [cbn in Hi; lia|]. destruct i as [|i].
  - cbn [firstn existsb nth]. rewrite orb_false_r, orb_false_l. apply Z.eqb_sym.
  - cbn [firstn existsb nth]. rewrite IH by (cbn in Hi; lia). rewrite orb_assoc. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section LOOP.
Context {fx : FPState}.
Variables (m0 : word -> option byte) (rom : word -> option byte) (AUXV RND : Z) (typs : list Z) (sp1 sec0 sec : Z).
Hypothesis HA1 : 8 <= AUXV.
Hypothesis HA2 : AUXV mod 8 = 0.
Hypothesis HA3 : AUXV + 16 * Z.of_nat (length typs) + 8 <= 2^47.
Hypothesis HTY : forall i, (i < length typs)%nat ->
     1 <= nth i typs 0 <= 2^64 - 1 /\
     rdn SEGS m0 (wa (AUXV + 16 * Z.of_nat i)) 8 = Some (word_to_le_bytes 8 (wa (nth i typs 0))) /\
     (nth i typs 0 = 25 -> rdn SEGS m0 (wa (AUXV + 16 * Z.of_nat i + 8)) 8 = Some (word_to_le_bytes 8 (wa RND))).
Hypothesis HTERM : rdn SEGS m0 (wa (AUXV + 16 * Z.of_nat (length typs))) 8 = Some (word_to_le_bytes 8 (wa 0)).
Hypothesis HR1 : 8 <= RND.
Hypothesis HR2 : RND mod 8 = 0.
Hypothesis HR3 : RND + 16 <= 2^47.
Hypothesis HSEC : rdn SEGS m0 (wa (RND + 8)) 8 = Some (word_to_le_bytes 8 (wa sec)).
Hypothesis Hsec : 0 <= sec <= 2^64 - 1.
Hypothesis Hsp1 : 2^20 <= sp1 <= 2^47.
Hypothesis Hsp1a : sp1 mod 16 = 0.
Hypothesis HAP : sp1 + 8 <= AUXV.
Hypothesis HRP : sp1 + 8 <= RND + 8.
Hypothesis HLIBC : rdn SEGS m0 (wa (0 + 621608)) 8 = Some (word_to_le_bytes 8 (wa AUXV)).
Hypothesis HW : forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m0 (wa (sp1 + 0 + d)) k = true.

Definition secv (i : nat) : Z := if existsb (Z.eqb 25) (firstn i typs) then sec else sec0.

Definition LINV (i : nat) (R : bvmap 5 word) (m : word -> option byte) : Prop :=
  getr R 9 = wa (16 * Z.of_nat i) /\ getr R 10 = wa AUXV /\ getr R 20 = wa 25 /\ getr R 2 = wa sp1 /\
  getr R 8 = wa 621600 /\ getr R 19 = wa 621712 /\
  (forall x, 0 <= x < 2^64 -> ~ (sp1 <= x < sp1 + 8) -> m (wa x) = m0 (wa x)) /\ mem_grows m0 m /\
  rdn SEGS m (wa sp1) 8 = Some (word_to_le_bytes 8 (wa (secv i))).

#[using="AUXV RND typs sp1"] Lemma mul16_mod : forall i, (16 * Z.of_nat i) mod 16 = 0.
Proof. LiaFast.lf_pins (fun (AUXV RND typs sp1 : LiaFast.U) => LiaFast.u0). intros i. rewrite Z.mul_comm. apply Z.mod_mul. lia. Qed.

#[using="AUXV RND typs sp1"] Lemma add_mod8 : forall a b, a mod 8 = 0 -> (16 * b) mod 8 = 0 -> (a + 16 * b) mod 8 = 0.
Proof. LiaFast.lf_pins (fun (AUXV RND typs sp1 : LiaFast.U) => LiaFast.u0). intros a b Ha Hb. rewrite Z.add_mod by lia. rewrite Ha, Hb. reflexivity. Qed.

#[using="RND HA1 HA2 HA3 HTY HTERM HR1 HR2 HR3 HSEC Hsec Hsp1 Hsp1a HAP HRP HLIBC HW"] Theorem auxv_loop : forall n i R m, (length typs - i = n)%nat -> (i <= length typs)%nat -> LINV i R m ->
  exists R' m', msteps SEGS (mkst R (wa 0x53ae4) m rom) (mkst R' (wa 0x53af4) m' rom) /\
    getr R' 2 = wa sp1 /\ getr R' 8 = wa 621600 /\ getr R' 19 = wa 621712 /\
    (forall k, In k [3; 4; 18; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R' (Z_to_bv 5 (Z.of_nat k)) = getr R (Z_to_bv 5 (Z.of_nat k))) /\
    (forall x, 0 <= x < 2^64 -> ~ (sp1 <= x < sp1 + 8) -> m' (wa x) = m0 (wa x)) /\ mem_grows m0 m' /\
    rdn SEGS m' (wa sp1) 8 = Some (word_to_le_bytes 8 (wa (secv (length typs)))).
Proof. LiaFast.lf_pins (fun (RND HA1 HA2 HA3 HTY HTERM HR1 HR2 HR3 HSEC Hsec Hsp1 Hsp1a HAP HRP HLIBC HW : LiaFast.U) => LiaFast.u0).
  induction n as [|n IH]; intros i R m En Hi (L9 & L10 & L20 & L2 & L8 & L19 & LM & LG & LT).
  all: assert (RD : forall a k, 0 <= a -> a + Z.of_nat k <= 2^64 -> (a + Z.of_nat k <= sp1 \/ sp1 + 8 <= a) -> rdn SEGS m (wa a) k = rdn SEGS m0 (wa a) k)
         by (intros a k Ha Hk Hd; apply rdn_frame_n; [exact Ha | exact Hk | intros x Hx; apply LM; lia]).
  - (* [comment removed for export] *)
    assert (Ei : i = length typs) by lia. subst i.
    assert (P : mil2_pre R m AUXV (16 * Z.of_nat (length typs)) 0).
    { constructor; [exact L9 | exact L10 | exact L20 | lia | lia | lia | exact HA2 | apply mul16_mod |].
      rewrite Z.add_0_r, RD by lia. exact HTERM. }
    destruct (mil2_pmlx R m rom AUXV (16 * Z.of_nat (length typs)) 0 P) as (R1 & Hms1 & A9 & A10 & A11 & A12 & A20 & K1).
    { cbn [OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_mmwz.AXF_mil2.RES_pmlx fst snd]. repeat (first [apply Forall_nil | apply Forall_cons]).
      all: apply sc_br_z; first [rewrite br_eq_z | rewrite br_ne_z]; cbn [zeval edenot].
      all: rewrite (zatom R (VALS_mil2 AUXV (16 * Z.of_nat (length typs)) 0) 34 0 eq_refl eq_refl) by lia; reflexivity. }
    change (mil2_mem_pmlx m R AUXV (16 * Z.of_nat (length typs)) 0) with m in Hms1.
    exists R1, m. split; [exact Hms1|].
    split; [regk K1 2%nat; exact L2|]. split; [regk K1 8%nat; exact L8|]. split; [regk K1 19%nat; exact L19|].
    split; [intros k Hk'; apply K1; clear - Hk'; klist Hk'|]. split; [exact LM|]. split; [exact LG | exact LT].
  - assert (Hlt : (i < length typs)%nat) by lia.
    destruct (HTY i Hlt) as (Ty1 & Ty2 & Ty3). set (typ := nth i typs 0) in *.
    assert (P : mil2_pre R m AUXV (16 * Z.of_nat i) typ).
    { constructor; [exact L9 | exact L10 | exact L20 | lia | lia | lia | exact HA2 | apply mul16_mod |].
      rewrite Z.add_0_r, RD by lia. exact Ty2. }
    destruct (Z.eq_dec typ 25) as [E25|N25].
    + (* [comment removed for export] *)
      destruct (mil2_pmlr R m rom AUXV (16 * Z.of_nat i) typ P) as (R1 & Hms1 & A9 & A10 & A11 & A12 & A20 & K1).
      { cbn [OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_mmwz.AXF_mil2.RES_pmlr fst snd]. repeat (first [apply Forall_nil | apply Forall_cons]).
        apply sc_br_z. rewrite br_eq_z. cbn [zeval edenot].
        rewrite (zatom R (VALS_mil2 AUXV (16 * Z.of_nat i) typ) 34 typ eq_refl eq_refl) by lia. rewrite E25. reflexivity. }
      change (mil2_mem_pmlr m R AUXV (16 * Z.of_nat i) typ) with m in Hms1.
      assert (Pr : mir_pre R1 m (AUXV + 16 * Z.of_nat i) RND sp1).
      { constructor; [regk K1 2%nat; exact L2 | exact A12 | lia | lia | lia | apply add_mod8; [exact HA2 | replace (16 * Z.of_nat i) with ((2 * Z.of_nat i) * 8) by ring; apply Z.mod_mul; lia] | exact Hsp1a |].
        rewrite RD by lia. exact (Ty3 E25). }
      destruct (mir_pmir R1 m rom (AUXV + 16 * Z.of_nat i) RND sp1 Pr ltac:(constructor)) as (R2 & Hms2 & B1 & B2 & B10 & B11 & B12 & K2).
      change (mir_mem_pmir m R1 (AUXV + 16 * Z.of_nat i) RND sp1) with m in Hms2.
      set (q := (RND + 8) / 4).
      assert (Eq : 4 * q = RND + 8).
      { unfold q. pose proof (Z.div_mod (RND + 8) 4 ltac:(lia)). assert ((RND + 8) mod 4 = 0).
        { apply Z.mod_divide in HR2; [|lia]. destruct HR2 as (k & ->). replace (k * 8 + 8) with ((2 * k + 2) * 4) by ring. apply Z.mod_mul. lia. }
        lia. }
      assert (Pc : mcp0_pre R2 m sp1 q sec).
      { constructor; [exact B1 | exact B10 | rewrite Eq; exact B11 | exact B12 | lia | lia | lia | exact Hsp1a | | |].
        - rewrite Z.add_0_r, Eq, RD by lia. exact HSEC.
        - intros d k Hd Hk'. apply (store_ok_mono SEGS k m0 m _ LG). exact (HW d k Hd Hk').
        - lia. }
      destruct (mcp0_pmcp0 R2 m rom sp1 q sec Pc ltac:(constructor)) as (R3 & Hms3 & C1 & C10 & C11 & C12 & C13 & C14 & K3).
      set (m3 := mcp0_mem_pmcp0 m R2 sp1 q sec) in *.
      assert (M3 : forall x, 0 <= x < 2^64 -> m3 (wa x) = wbytes m (wa sp1) (word_to_le_bytes 8 (wa sec)) (wa x))
        by (intros x Hx; unfold m3; apply mcp0_pt; lia).
      assert (LM3 : forall x, 0 <= x < 2^64 -> ~ (sp1 <= x < sp1 + 8) -> m3 (wa x) = m0 (wa x)).
      { intros x Hx Hn. rewrite M3 by exact Hx. rewrite MngWb.wbytes_out by side. exact (LM x Hx Hn). }
      assert (Pi : mic2_pre R3 m3 AUXV (16 * Z.of_nat i)).
      { constructor; [| | lia | lia |].
        - regk K3 8%nat. regk K2 8%nat. regk K1 8%nat. exact L8.
        - regk K3 9%nat. regk K2 9%nat. exact A9.
        - rewrite (rdn_frame_n m0 m3) by (first [(intros x Hx; cbn [Z.of_nat Pos.of_succ_nat] in Hx; apply LM3; lia) | lia]). exact HLIBC. }
      destruct (mic2_pmic R3 m3 rom AUXV (16 * Z.of_nat i) Pi ltac:(constructor)) as (R4 & Hms4 & D8 & D9 & D10 & K4).
      change (mic2_mem_pmic m3 R3 AUXV (16 * Z.of_nat i)) with m3 in Hms4.
      assert (LI : LINV (S i) R4 m3).
      { split; [rewrite D9; f_equal; lia|]. split; [exact D10|].
        split; [regk K4 20%nat; regk K3 20%nat; regk K2 20%nat; exact A20|].
        split; [regk K4 2%nat; regk K3 2%nat; exact B2|]. split; [exact D8|].
        split; [regk K4 19%nat; regk K3 19%nat; regk K2 19%nat; regk K1 19%nat; exact L19|].
        split; [exact LM3|]. split.
        - intros x Hx. rewrite <- (wa_u x) in Hx |- *. rewrite M3 by apply OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngU.MngLedger.u_range. apply (wbytes_grows _ m). exact (LG _ Hx).
        - rewrite (rdn_frame_n (wbytes m (wa sp1) (word_to_le_bytes 8 (wa sec))) m3) by (first [(intros x Hx; apply M3; lia) | lia]).
          unfold secv. rewrite existsb_firstn_S by exact Hlt. fold typ. rewrite E25, Z.eqb_refl, orb_true_r.
          apply rdn_wbytes_hit8. rewrite u_wa_small by lia. lia. }
      destruct (IH (S i) R4 m3 ltac:(lia) ltac:(lia) LI) as (R' & m' & Hms' & E2 & E8 & E19 & KE & EM & EG & ET).
      exists R', m'. split; [exact (msteps_trans SEGS _ _ _ Hms1 (msteps_trans SEGS _ _ _ Hms2 (msteps_trans SEGS _ _ _ Hms3 (msteps_trans SEGS _ _ _ Hms4 Hms'))))|].
      do 3 (split; [assumption|]). split; [|split; [exact EM | split; [exact EG | exact ET]]].
      intros k Hk'. rewrite (KE k Hk'), (K4 k ltac:(clear - Hk'; klist Hk')), (K3 k ltac:(clear - Hk'; klist Hk')),
        (K2 k ltac:(clear - Hk'; klist Hk')), (K1 k ltac:(clear - Hk'; klist Hk')). reflexivity.
    + (* [comment removed for export] *)
      destruct (mil2_pmlc R m rom AUXV (16 * Z.of_nat i) typ P) as (R1 & Hms1 & A9 & A10 & A11 & A12 & A20 & K1).
      { cbn [OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_mmwz.AXF_mil2.RES_pmlc fst snd]. repeat (first [apply Forall_nil | apply Forall_cons]).
        all: apply sc_br_z; first [rewrite br_eq_z | rewrite br_ne_z]; cbn [zeval edenot].
        all: rewrite (zatom R (VALS_mil2 AUXV (16 * Z.of_nat i) typ) 34 typ eq_refl eq_refl) by lia.
        all: rewrite (Z.mod_small typ) by lia; cbn [Z.modulo]; first [ (apply negb_true_iff; apply Z.eqb_neq; lia) | (apply Z.eqb_neq; exact N25) ]. }
      change (mil2_mem_pmlc m R AUXV (16 * Z.of_nat i) typ) with m in Hms1.
      assert (LI : LINV (S i) R1 m).
      { split; [rewrite A9; f_equal; lia|]. split; [exact A10|]. split; [exact A20|].
        split; [regk K1 2%nat; exact L2|]. split; [regk K1 8%nat; exact L8|]. split; [regk K1 19%nat; exact L19|].
        split; [exact LM|]. split; [exact LG|].
        unfold secv. rewrite existsb_firstn_S by exact Hlt. fold typ. replace (typ =? 25) with false by (symmetry; apply Z.eqb_neq; exact N25).
        rewrite orb_false_r. exact LT. }
      destruct (IH (S i) R1 m ltac:(lia) ltac:(lia) LI) as (R' & m' & Hms' & E2 & E8 & E19 & KE & EM & EG & ET).
      exists R', m'. split; [exact (msteps_trans SEGS _ _ _ Hms1 Hms')|].
      do 3 (split; [assumption|]). split; [|split; [exact EM | split; [exact EG | exact ET]]].
      intros k Hk'. rewrite (KE k Hk'), (K1 k ltac:(clear - Hk'; klist Hk')). reflexivity.
Qed.
End LOOP.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma alloc_meta_init : forall s, alloc_meta s = alloc_meta (set_init_done true s).
Proof. intros s. unfold alloc_meta. cbn. reflexivity. Qed.

(* [comment removed for export] *)
Definition AMI (L : layout) (m : word -> option byte) (sp0 : Z) : Prop :=
  exists AUXV RND typs, init_env L m AUXV RND typs /\ sp0 <= AUXV /\ sp0 <= RND + 8.

Lemma existsb_all25 : forall l, In 25 l -> existsb (Z.eqb 25) (firstn (length l) l) = true.
Proof. intros l H. rewrite firstn_all. apply existsb_exists. exists 25. split; [exact H | apply Z.eqb_refl]. Qed.

(* [comment removed for export] *)
Lemma nc_si_wr : forall L s m sp0 K d k, NC L [] [] s m sp0 K -> 0 <= d -> d + Z.of_nat k <= 12 ->
  store_ok SEGS m (wa (621720 + d)) k = true.
Proof.
  intros L s m sp0 K d k N Hd Hk. pose proof (nc_ctx _ _ _ _ _ _ _ N) as Hctx.
  apply (store_ok_of_bytes SEGS m 621720 12); [|exact Hd | exact Hk].
  intros j Hj. destruct (Z_lt_le_dec j 8) as [D|D].
  - pose proof (holds_wview SEGS L m (MCell (LCtx CTX_secret) 8 (if st_init_done s then VSec else VZ 0)) j
      (nc_ctx_holds L s m sp0 K (MCell (LCtx CTX_secret) 8 (if st_init_done s then VSec else VZ 0)) N ltac:(in_ctx13))
      ltac:(destruct (st_init_done s); intros z E; discriminate) ltac:(cbn; lia)) as W.
    cbn [mc_loc loc_addr] in W. rewrite Hctx in W. exact W.
  - pose proof (holds_wview SEGS L m (MCell (LCtx CTX_init_done) 4 (VZ (if st_init_done s then 1 else 0))) (j - 8)
      (nc_ctx_holds L s m sp0 K (MCell (LCtx CTX_init_done) 4 (VZ (if st_init_done s then 1 else 0))) N ltac:(in_ctx13))
      ltac:(intros z E; discriminate) ltac:(cbn; lia)) as W.
    cbn [mc_loc loc_addr] in W. rewrite Hctx in W. unfold CTX_init_done in W. replace (621720 + j) with (0x97c98 + 8 + (j - 8)) by ring. exact W.
Qed.

Definition cnew_init : list mcell := [MCell (LCtx CTX_secret) 8 VSec; MCell (LCtx CTX_init_done) 4 (VZ 1)].

Lemma init_cov_ctx : forall s c, In c (ctx_cells (set_init_done true s)) -> In c (ctx_cells s) \/ In c cnew_init.
Proof.
  intros s c Hc. unfold ctx_cells in Hc.
  cbn [st_init_done st_mmap_counter st_free_meta_head st_areas st_avail_meta st_avail_meta_count
      st_avail_meta_area_count st_meta_alloc_shift st_area_head st_area_tail st_avail_meta_areas st_seq st_brk st_active st_usage
      st_unmap_seq st_bounces set_init_done] in Hc.
  apply in_app_iff in Hc as [Hc|Hc]; [|left; unfold ctx_cells; apply in_app_iff; right; exact Hc].
  cbn [In] in Hc.
  repeat (destruct Hc as [<-|Hc]; [first [ (left; unfold ctx_cells; apply in_app_iff; left; cbn [In]; solve [memb])
                                        | (right; unfold cnew_init; cbn [In]; solve [memb]) ] |]).
  destruct Hc.
Qed.

Lemma init_rev_ctx : forall s c, In c (ctx_cells s) ->
  In c (ctx_cells (set_init_done true s)) \/ exists c', In c' cnew_init /\ mc_loc c' = mc_loc c /\ mc_w c' = mc_w c.
Proof.
  intros s c Hc. unfold ctx_cells in Hc.
  apply in_app_iff in Hc as [Hc|Hc]; [|left; unfold ctx_cells; apply in_app_iff; right; exact Hc].
  cbn [In] in Hc.
  repeat (destruct Hc as [<-|Hc]; [first [ (left; unfold ctx_cells; apply in_app_iff; left;
       cbn [st_init_done st_mmap_counter st_free_meta_head st_areas st_avail_meta st_avail_meta_count
            st_avail_meta_area_count st_meta_alloc_shift st_area_head st_area_tail st_avail_meta_areas st_seq st_brk set_init_done In]; solve [memb])
     | (right; exists (MCell (LCtx CTX_secret) 8 VSec); split; [unfold cnew_init; cbn [In]; left; reflexivity | split; reflexivity])
     | (right; exists (MCell (LCtx CTX_init_done) 4 (VZ 1)); split; [unfold cnew_init; cbn [In]; right; left; reflexivity | split; reflexivity]) ] |]).
  destruct Hc.
Qed.

Lemma init_areas_cells : forall s l, areas_cells (set_init_done true s) l = areas_cells s l.
Proof. intros s l. apply areas_cells_ext. intros q. reflexivity. Qed.

Lemma init_cov : forall s c, In c (image (set_init_done true s)) -> In c (image s) \/ In c cnew_init.
Proof.
  intros s c Hc. unfold image in Hc. apply in_app_iff in Hc as [Hc|Hc].
  - destruct (init_cov_ctx s c Hc) as [H|H]; [left; apply ctx_in_image; exact H | right; exact H].
  - left. unfold image. apply in_app_iff. right. replace (st_areas (set_init_done true s)) with (st_areas s) in Hc by reflexivity.
    rewrite init_areas_cells in Hc. exact Hc.
Qed.

Lemma init_rev : forall s c, In c (image s) ->
  In c (image (set_init_done true s)) \/ exists c', In c' cnew_init /\ mc_loc c' = mc_loc c /\ mc_w c' = mc_w c.
Proof.
  intros s c Hc. unfold image in Hc. apply in_app_iff in Hc as [Hc|Hc].
  - destruct (init_rev_ctx s c Hc) as [H|H]; [left; apply ctx_in_image; exact H | right; exact H].
  - left. unfold image. apply in_app_iff. right. replace (st_areas (set_init_done true s)) with (st_areas s) by reflexivity.
    rewrite init_areas_cells. exact Hc.
Qed.

Lemma init_in : forall s c, In c cnew_init -> In c (image (set_init_done true s)).
Proof.
  intros s c Hc. apply ctx_in_image. unfold cnew_init in Hc. cbn [In] in Hc. unfold ctx_cells. apply in_app_iff. left.
  cbn [st_init_done set_init_done In]. destruct Hc as [<-|[<-|[]]]; solve [memb].
Qed.

Section WKI.
Context {fx : FPState}.
Variable FORB : list (Z * Z).
Hypothesis HFORB : forall a n, 0 < n -> Forall (fun r => ranges_disjoint (a, n) r) FORB -> ranges_disjoint (a, n) (0x10000, 0x89000).
Hypothesis WOR : forall HTOP X R U L0 s0 m0 (regs0 : bvmap 5 word) L s m Rg rom sp0 K can ra r o rg
    (Kt : Z -> itree astate (option sptr * astate)),
  CUT HTOP X R U L s m sp0 K -> GROW sp0 K L0 s0 m0 L s m -> 1152 <= K ->
  am_frame Rg m sp0 can ra (bv_unsigned (getr regs0 8)) (bv_unsigned (getr regs0 9))
    (bv_unsigned (getr regs0 18)) (bv_unsigned (getr regs0 19)) (bv_unsigned (getr regs0 20)) ->
  getr regs0 1 = wa ra -> getr regs0 2 = wa sp0 -> (ra = 0x542a0 \/ ra = 0x53ec4) ->
  (forall k, In k [3;4;21;22;23;24;25;26;27]%nat -> getr Rg (Z_to_bv 5 (Z.of_nat k)) = getr regs0 (Z_to_bv 5 (Z.of_nat k))) ->
  getr Rg 1 = wa 343320 -> getr Rg 9 = wa (ly_reg L r + o) -> getr Rg 10 = wa (ly_reg L r + o) ->
  getr Rg 11 = wa 4096 -> getr Rg 12 = wa 3 ->
  st_init_done s = true -> st_free_meta_head s = None -> st_avail_meta_count s = 0 -> 0 < st_avail_meta_area_count s ->
  st_avail_meta_areas s = SP r o -> region_of s r = Some rg ->
  rdn SEGS m (wa 621648) 8 = Some (word_to_le_bytes 8 (wa 4096)) ->
  Kt 1 = IRet (Some (padd (SP r o) AREA_HDR), s_opn (SP r o) (s_res1 s r rg o)) ->
  wk SEGS FORB HTOP rom L Rg (wa 0x551cc) m (IAsk (KMprotect (SP r o)) s Kt)
     (am_qpost HTOP X R U L0 s0 m0 regs0 sp0 K ra).

#[using="HFORB WOR"] Theorem wk_init : forall HTOP X R U L s m (regs : bvmap 5 word) rom sp0 K ra,
  CUT HTOP X R U L s m sp0 K -> 1152 <= K -> getr regs 2 = wa sp0 -> getr regs 1 = wa ra -> (ra = 0x542a0 \/ ra = 0x53ec4) ->
  rdn SEGS m (wa 621648) 8 = Some (word_to_le_bytes 8 (wa 4096)) ->
  PGSZ <= ly_brk0 L -> ly_brk0 L mod PGSZ = 0 -> ly_brk0 L <= HTOP ->
  st_init_done s = false -> AMI L m sp0 ->
  wk SEGS FORB HTOP rom L regs (wa 0x53a60) m (alloc_meta s) (am_qpost HTOP X R U L s m regs sp0 K ra).
Proof. LiaFast.lf_pins (fun (HFORB WOR : LiaFast.U) => LiaFast.u0).
  intros HTOP X R U L s m regs rom sp0 K ra C HK R2 R1 Hra Mpg B1 B2 B3 Hini (AUXV & RND & typs & IE & HAU & HRN).
  change (hide (ra = 0x542a0 \/ ra = 0x53ec4)) in Hra.
  pose proof C as [HI HX N HG HD HT HTB].
  pose proof (nc_ctx _ _ _ _ _ _ _ N) as Hctx. pose proof (nc_sp1 _ _ _ _ _ _ _ N) as Hsp1. pose proof (nc_sp2 _ _ _ _ _ _ _ N) as Hsp2.
  pose proof (nc_sp3 _ _ _ _ _ _ _ N) as Hsp3.
  pose proof (inv_ctx HI) as CT. unfold ctx_ok in CT. destruct CT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & C12).
  destruct (C12 Hini) as (Hmt & Har & Hbk & Hac).
  assert (Hf : st_free_meta_head s = None).
  { destruct (st_free_meta_head s) as [fm|] eqn:E; [|reflexivity]. exfalso.
    destruct (inv_rings HI) as ((ms & FR & _) & _). rewrite E in FR.
    destruct (ring_head_In _ _ _ FR) as [Hin _]. destruct (ring_links _ _ _ fm FR Hin) as (p' & n' & El).
    unfold flinks, MTX, MT in El. rewrite Hmt in El. cbn in El. destruct (memb fm X); discriminate El. }
  assert (Hc : st_avail_meta_count s = 0) by (pose proof (inv_keys HI) as (_ & _ & K3 & _); exact (K3 Har)).
  destruct IE as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11).
  assert (HA1 : 8 <= AUXV) by (pose proof (Z.div_mod AUXV 8 ltac:(lia)); lia).
  assert (HR1 : 8 <= RND) by (pose proof (Z.div_mod RND 8 ltac:(lia)); lia).
  set (sp1 := sp0 - 64) in *.
  assert (Hsp1a : sp1 mod 16 = 0).
  { unfold sp1. clear - Hsp3. apply Z.mod_divide in Hsp3; [|lia]. destruct Hsp3 as (k & ->). replace (k * 16 - 64) with ((k - 4) * 16) by ring. apply Z.mod_mul. lia. }
  (* [comment removed for export] *)
  destruct (seg_amp L s m regs rom sp0 K N R2) as (Rg & can & Hms1 & F1 & Kp1 & MO1 & MG1).
  set (m1 := am_mem0 m regs sp0 can) in *.
  assert (C1 : CUT HTOP X R U L s m1 sp0 K) by (apply (CUT_stack HTOP X R U L s m m1 sp0 K C MG1); intros x Hx Hn; apply MO1; [exact Hx | clear - Hn HK; lia]).
  assert (GR1 : GROW sp0 K L s m L s m1).
  { apply GROW_stack; [|clear - Hsp1; lia]. intros x Hx Hne. destruct (range_dec x (sp0 - 56) 56) as [I|I]; [clear - I HK; lia|]. exfalso. apply Hne. apply MO1; [exact Hx | clear - I; lia]. }
  pose proof C1 as [_ _ N1 _ _ _ _]. pose proof (nc_stk _ _ _ _ _ _ _ N1) as HSTK1.
  assert (STK : forall a k, sp0 - K <= a -> a + Z.of_nat k <= sp0 -> store_ok SEGS m1 (wa a) k = true).
  { intros a k Ha Hk. apply HSTK1; rewrite !u_wa_small by lia; lia. }
  assert (Rra : bv_unsigned (getr regs 1) = ra) by (rewrite R1; apply u_wa_small; clear - Hra; unfold hide in Hra; destruct Hra as [-> | ->]; lia).
  rewrite Rra in F1.
  (* [comment removed for export] *)
  assert (Mid : rdn SEGS m1 (wa (0 + 621728)) 4 = Some (word_to_le_bytes 4 (wa 0))).
  { pose proof (nc_ctx_rd L s m1 sp0 K (MCell (LCtx CTX_init_done) 4 (VZ (if st_init_done s then 1 else 0))) N1 ltac:(in_ctx13)
                  ltac:(intros z E; discriminate E) ltac:(cbn; lia)) as H. cbn [mc_loc mc_w mc_val loc_addr sval_num] in H. rewrite Hctx, Hini in H. exact H. }
  assert (MAU : rdn SEGS m1 (wa (0 + 621608)) 8 = Some (word_to_le_bytes 8 (wa AUXV))).
  { rewrite (rdn_frame_n m m1) by (first [(intros x Hx; cbn [Z.of_nat Pos.of_succ_nat] in Hx; apply MO1; lia) | lia]). exact E1. }
  assert (P0 : mi0_pre Rg m1 sp1 AUXV).
  { constructor; [ | exact (mf_R19 _ _ _ _ _ _ _ _ _ _ F1) | lia | lia | exact Hsp1a | exact Mid | exact MAU | | lia].
    - rewrite (mf_R2 _ _ _ _ _ _ _ _ _ _ F1). unfold sp1. f_equal; ring.
    - intros d k Hd Hk'. apply STK; unfold sp1 in *; lia. }
  destruct (mi0_pmi0 Rg m1 rom sp1 AUXV P0 ltac:(constructor)) as (Ri & Hms2 & I2 & I8 & I9 & I10 & I11 & I12 & I19 & I20 & Ki).
  set (m2 := mi0_mem_pmi0 m1 Rg sp1 AUXV) in *.
  assert (MO2 : forall x, 0 <= x < 2^64 -> ~ (sp1 <= x < sp1 + 8) -> m2 (wa x) = m1 (wa x))
    by (intros x Hx Hn; unfold m2, mi0_mem_pmi0; rewrite MngWb.wbytes_out by side; reflexivity).
  assert (MG2 : mem_grows m1 m2) by (unfold m2, mi0_mem_pmi0; apply wbytes_grows).
  assert (FR2 : forall a k, sp0 <= a -> a + Z.of_nat k <= 2^64 -> rdn SEGS m2 (wa a) k = rdn SEGS m (wa a) k).
  { intros a k Ha Hk. apply rdn_frame_n; [lia | exact Hk |]. intros x Hx. rewrite MO2 by (first [(unfold sp1; lia) | lia]). apply MO1; lia. }
  set (sec := ly_sec L mod 2^64).
  assert (Hsec : 0 <= sec <= 2^64 - 1) by (unfold sec; pose proof (Z.mod_pos_bound (ly_sec L) (2^64) ltac:(lia)); lia).
  assert (HTY : forall i, (i < length typs)%nat ->
     1 <= nth i typs 0 <= 2^64 - 1 /\
     rdn SEGS m2 (wa (AUXV + 16 * Z.of_nat i)) 8 = Some (word_to_le_bytes 8 (wa (nth i typs 0))) /\
     (nth i typs 0 = 25 -> rdn SEGS m2 (wa (AUXV + 16 * Z.of_nat i + 8)) 8 = Some (word_to_le_bytes 8 (wa RND)))).
  { intros i Hi'. destruct (E5 i Hi') as (T1 & T2 & T3). split; [exact T1|]. split.
    - rewrite FR2 by lia. exact T2.
    - intros E25. rewrite FR2 by lia. exact (T3 E25). }
  assert (HTERM : rdn SEGS m2 (wa (AUXV + 16 * Z.of_nat (length typs))) 8 = Some (word_to_le_bytes 8 (wa 0))) by (rewrite FR2 by lia; exact E6).
  assert (HSEC : rdn SEGS m2 (wa (RND + 8)) 8 = Some (word_to_le_bytes 8 (wa sec))) by (rewrite FR2 by lia; unfold sec; rewrite <- wa_mod64; exact E11).
  assert (HLIBC : rdn SEGS m2 (wa (0 + 621608)) 8 = Some (word_to_le_bytes 8 (wa AUXV))).
  { rewrite (rdn_frame_n m1 m2) by (first [(intros x Hx; cbn [Z.of_nat Pos.of_succ_nat] in Hx; apply MO2; [lia | unfold sp1; lia]) | lia]). exact MAU. }
  assert (HW : forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m2 (wa (sp1 + 0 + d)) k = true).
  { intros d k Hd Hk'. apply (store_ok_mono SEGS k m1 m2 _ MG2). apply STK; unfold sp1 in *; lia. }
  assert (LI0 : LINV m2 AUXV typs sp1 (1103515245 * sp1) sec 0%nat Ri m2).
  { split; [exact I9|]. split; [exact I10|]. split; [exact I20|]. split; [exact I2|]. split; [exact I8|]. split; [exact I19|].
    split; [intros; reflexivity|]. split; [apply mem_grows_refl|].
    unfold secv. cbn [firstn existsb]. unfold m2, mi0_mem_pmi0. replace (wa sp1) with (wa (sp1 + 0)) by (f_equal; ring).
    apply rdn_wbytes_hit8. rewrite u_wa_small by (unfold sp1; lia). unfold sp1; lia. }
  destruct (auxv_loop m2 rom AUXV RND typs sp1 (1103515245 * sp1) sec HA1 E3 E4 HTY HTERM HR1 E9 E10 HSEC Hsec ltac:(unfold sp1; lia) Hsp1a
              ltac:(unfold sp1; lia) ltac:(unfold sp1; lia) HLIBC HW (length typs - 0) 0%nat Ri m2 eq_refl ltac:(lia) LI0)
    as (Rl & ml & Hms3 & G2 & G8 & G19 & KG & GM & GG & GT).
  unfold secv in GT. rewrite existsb_all25 in GT by exact E7.
  assert (MOl : forall x, 0 <= x < 2^64 -> ~ (sp1 <= x < sp1 + 8) -> ml (wa x) = m1 (wa x)) by (intros x Hx Hn; rewrite GM, MO2 by assumption; reflexivity).
  assert (MGl : mem_grows m1 ml) by exact (mem_grows_trans m1 m2 ml MG2 GG).
  (* [comment removed for export] *)
  assert (Mfm : rdn SEGS ml (wa (0 + 621736)) 8 = Some (word_to_le_bytes 8 (wa 0))).
  { pose proof (nc_ctx_rd L s m1 sp0 K (MCell (LCtx CTX_free_meta_head) 8 (optr (st_free_meta_head s))) N1 ltac:(in_ctx13)
      ltac:(intros z E; cbn [mc_val optr] in E; destruct (st_free_meta_head s); discriminate) ltac:(cbn; lia)) as H.
    cbn [mc_loc mc_w mc_val loc_addr] in H. rewrite Hctx, sval_optr, Hf in H.
    rewrite (rdn_frame_n m1 ml) by (first [(intros x Hx; cbn [Z.of_nat Pos.of_succ_nat] in Hx; apply MOl; [lia | unfold sp1; lia]) | lia]). exact H. }
  assert (Mpgl : rdn SEGS ml (wa (0 + 621648)) 8 = Some (word_to_le_bytes 8 (wa 4096))).
  { rewrite (rdn_frame_n m ml) by (first [(intros x Hx; cbn [Z.of_nat Pos.of_succ_nat] in Hx; rewrite MOl by (first [lia | unfold sp1; lia]); apply MO1; lia) | lia]). exact Mpg. }
  assert (Wsi : forall d k, 0 <= d -> d + Z.of_nat k <= 12 -> store_ok SEGS ml (wa (0 + 621720 + d)) k = true).
  { intros d k Hd Hk'. apply (store_ok_mono SEGS k m1 ml _ MGl). exact (nc_si_wr L s m1 sp0 K d k N1 Hd Hk'). }
  assert (P4 : mix_pre Rl ml sp1 sec).
  { constructor; [exact G2 | exact G8 | exact G19 | unfold sp1; lia | exact Hsec | exact Hsp1a | rewrite Z.add_0_r; exact GT | exact Mpgl | exact Mfm | exact Wsi | unfold sp1; lia]. }
  destruct (mix_pmix Rl ml rom sp1 sec P4 ltac:(constructor)) as (Rx & Hms4 & X2 & X8 & X10 & X11 & X19 & Kx).
  set (mx := mix_mem_pmix ml Rl sp1 sec) in *.
  assert (MOx : forall x, 0 <= x < 2^64 -> ~ (sp1 <= x < sp1 + 8) -> ~ (621720 <= x < 621732) -> mx (wa x) = m1 (wa x)).
  { intros x Hx H1 H2. unfold mx, mix_mem_pmix. rewrite !MngWb.wbytes_out by side. exact (MOl x Hx H1). }
  assert (MGx : mem_grows m1 mx) by (unfold mx, mix_mem_pmix; apply (mem_grows_trans m1 ml); [exact MGl | apply (mem_grows_trans _ (wbytes ml (wa (0 + 621720)) (word_to_le_bytes 8 (wa sec)))); apply wbytes_grows]).
  (* [comment removed for export] *)
  set (s' := set_init_done true s).
  assert (HIs : Inv X R U s') by exact (Inv_set_init_done X R U s HI).
  assert (NEW : Forall (cell_holds L (bview SEGS mx)) cnew_init).
  { unfold cnew_init. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    - assert (H1 : cell_holds L (bview SEGS (wbytes ml (wa (0 + 621720)) (word_to_le_bytes 8 (wa sec)))) (MCell (LCtx CTX_secret) 8 VSec)).
      { replace (wa (0 + 621720)) with (wa (loc_addr L (mc_loc (MCell (LCtx CTX_secret) 8 VSec)))) by (cbn [mc_loc loc_addr]; rewrite Hctx; reflexivity).
        change 8%nat with (mc_w (MCell (LCtx CTX_secret) 8 VSec)).
        apply holds_wb; cbn [mc_val mc_w mc_loc loc_addr sval_num]; rewrite ?Hctx; unfold CTX_secret;
          first [ (intros z E; discriminate E) | (unfold sec; apply Z.mod_mod; lia) | lia ]. }
      apply (cell_holds_frame L _ _ (MCell (LCtx CTX_secret) 8 VSec) ltac:(cbn; lia) H1).
      intros a Ha. unfold in_rng, cell_range in Ha. cbn [fst snd mc_loc mc_w loc_addr] in Ha.
      rewrite Hctx in Ha. unfold CTX_secret in Ha. unfold mx, mix_mem_pmix. apply MngWb.bview_ext. rewrite MngWb.wbytes_out by side. reflexivity.
    - unfold mx, mix_mem_pmix.
      replace (wa (0 + 621728)) with (wa (loc_addr L (mc_loc (MCell (LCtx CTX_init_done) 4 (VZ 1))))) by (cbn [mc_loc loc_addr]; rewrite Hctx; reflexivity).
      change 4%nat with (mc_w (MCell (LCtx CTX_init_done) 4 (VZ 1))).
      apply holds_wb; cbn [mc_val mc_w mc_loc loc_addr sval_num]; rewrite ?Hctx; unfold CTX_init_done;
        first [ (intros z E; discriminate E) | lia | reflexivity ]. }
  destruct (silent_step' HTOP X R U X R U L s s' m1 mx sp0 K cnew_init C1 HIs HX HG HD (RMONO_refl s)) as (C2 & G2').
  { intros rg Hrg. left. exact Hrg. }
  { intros c Hc0. exact (init_cov s c Hc0). }
  { intros c Hc0. exact (init_in s c Hc0). }
  { intros c Hc0. destruct (init_rev s c Hc0) as [H|(c' & Hc' & El & Ew)]; [left; exact H | right].
    exists c'. split; [exact Hc'|]. unfold cell_range. rewrite El, Ew. reflexivity. }
  { exact NEW. }
  { exact MGx. }
  { intros x Hx Hne. destruct (decide (sp1 <= x < sp1 + 8)) as [D1|D1]; [left; unfold sp1 in D1; clear - D1 HK; lia|].
    destruct (decide (621720 <= x < 621732)) as [D2|D2]; [|exfalso; exact (Hne (MOx x Hx D1 D2))].
    right. destruct (Z_lt_le_dec x 621728) as [D3|D3].
    - exists (MCell (LCtx CTX_secret) 8 VSec). split; [unfold cnew_init; cbn [In]; left; reflexivity|].
      unfold in_rng, cell_range. cbn [fst snd mc_loc mc_w loc_addr]. rewrite Hctx. unfold CTX_secret. cbn [Z.of_nat Pos.of_succ_nat]. lia.
    - exists (MCell (LCtx CTX_init_done) 4 (VZ 1)). split; [unfold cnew_init; cbn [In]; right; left; reflexivity|].
      unfold in_rng, cell_range. cbn [fst snd mc_loc mc_w loc_addr]. rewrite Hctx. unfold CTX_init_done. cbn [Z.of_nat Pos.of_succ_nat]. lia. }
  (* [comment removed for export] *)
  assert (Macnt : rdn SEGS mx (wa (0 + 621752)) 8 = Some (word_to_le_bytes 8 (wa 0))).
  { pose proof (nc_amc_rd L s m1 sp0 K N1) as H. rewrite Hc in H.
    rewrite (rdn_frame_n m1 mx) by (first [(intros x Hx; cbn [Z.of_nat Pos.of_succ_nat] in Hx; apply MOx; [lia | unfold sp1; lia | lia]) | lia]). exact H. }
  assert (Mam : rdn SEGS mx (wa (0 + 621744)) 8 = Some (word_to_le_bytes 8 (wa 0))).
  { pose proof (nc_ctx_rd L s m1 sp0 K (MCell (LCtx CTX_avail_meta) 8 (match st_areas s with [] => VZ 0 | _ => VP (st_avail_meta s) end)) N1 ltac:(in_ctx13)
      ltac:(intros z E; destruct (st_areas s); discriminate) ltac:(cbn; lia)) as H.
    cbn [mc_loc mc_w mc_val loc_addr] in H. rewrite Hctx, Har in H. cbn [sval_num] in H.
    rewrite (rdn_frame_n m1 mx) by (first [(intros x Hx; cbn [Z.of_nat Pos.of_succ_nat] in Hx; apply MOx; [lia | unfold sp1; lia | lia]) | lia]). exact H. }
  assert (Wam : forall d k, 0 <= d -> d + Z.of_nat k <= 16 -> store_ok SEGS mx (wa (0 + 621744 + d)) k = true).
  { intros d k Hd Hk'. apply (store_ok_mono SEGS k m1 mx _ MGx). exact (nc_am_wr L s m1 sp0 K d k N1 Hd Hk'). }
  assert (P5 : mt2_pre Rx mx 0 0) by (constructor; [exact X19 | clear; lia | clear; lia | exact Macnt | exact Mam | exact Wam]).
  destruct (mt2_pmt2z Rx mx rom 0 0 P5) as (Rq & Hms5 & B11 & B19 & Bk5).
  { cbn [OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_eez.AXF_mt2.RES_pmt2z fst snd]. repeat (first [apply Forall_nil | apply Forall_cons]). apply sc_br_z. rewrite br_eq_z.
    cbn [zeval edenot]. rewrite (zatom Rx (VALS_mt2 0 0) 32 0 eq_refl eq_refl) by lia. reflexivity. }
  change (mt2_mem_pmt2z mx Rx 0 0) with mx in Hms5.
  assert (KA : forall k, In k [3;4;21;22;23;24;25;26;27]%nat -> getr Rq (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
  { intros k Hk'. rewrite (Bk5 k ltac:(clear - Hk'; klist Hk')), (Kx k ltac:(clear - Hk'; klist Hk')), (KG k ltac:(clear - Hk'; klist Hk')),
      (Ki k ltac:(clear - Hk'; klist Hk')), (Kp1 k ltac:(clear - Hk'; klist Hk')). reflexivity. }
  assert (Fq : am_frame Rq mx sp0 can ra (bv_unsigned (getr regs 8)) (bv_unsigned (getr regs 9))
                 (bv_unsigned (getr regs 18)) (bv_unsigned (getr regs 19)) (bv_unsigned (getr regs 20))).
  { apply (am_frame_mem Rq m1); [| intros x Hx; apply MOx; [lia | unfold sp1; lia | lia] | intros x Hx; apply MOx; [lia | unfold sp1; lia | lia]].
    apply (am_frame_regs Rg Rq m1 sp0 can _ _ _ _ _ _ F1).
    - regk Bk5 2%nat. litr2 X2. rewrite (mf_R2 _ _ _ _ _ _ _ _ _ _ F1). unfold sp1. f_equal; ring.
    - regk Bk5 18%nat. regk Kx 18%nat. regk KG 18%nat. regk Ki 18%nat. reflexivity.
    - rewrite B19. exact (eq_sym (mf_R19 _ _ _ _ _ _ _ _ _ _ F1)). }
  assert (Q8 : getr Rq 8 = wa 4096) by (regk Bk5 8%nat; exact X8).
  assert (Mpgx : rdn SEGS mx (wa 621648) 8 = Some (word_to_le_bytes 8 (wa 4096))).
  { rewrite (rdn_frame_n m1 mx) by (first [(intros x Hx; cbn [Z.of_nat Pos.of_succ_nat] in Hx; apply MOx; [lia | unfold sp1; lia | lia]) | lia]).
    rewrite (rdn_frame_n m m1) by (first [(intros x Hx; cbn [Z.of_nat Pos.of_succ_nat] in Hx; apply MO1; lia) | lia]). exact Mpg. }
  rewrite alloc_meta_init. fold s'.
  apply (wk_msteps SEGS FORB HTOP rom _ _ _ _ _ _ _ _ _
           (msteps_trans SEGS _ _ _ Hms1 (msteps_trans SEGS _ _ _ Hms2 (msteps_trans SEGS _ _ _ Hms3 (msteps_trans SEGS _ _ _ Hms4 Hms5))))).
  exact (wk_bn_tail FORB HFORB WOR HTOP X R U L s m regs L s' mx Rq rom sp0 K can ra C2 (GROW_trans sp0 K L s m L s m1 L s' mx GR1 G2') HK Fq R1 R2 Hra Q8 KA
           Mpgx B1 B2 B3 eq_refl Hf Hc Hac Hbk).
Qed.
End WKI.
