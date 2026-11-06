(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk SeqExec AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require Import MallocModel MallocInv.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AxMng AxBits MngZ MngHeap MngNtfM MngWb AxTry.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require MngHeap.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AXG_as1 AXG_ag0 AXG_ag1.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AXF_taez.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AXF_taez.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AXG_ag1.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AXG_ag1.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AXG_ag1.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AXF_taez.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AXF_taez.
Import OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AxMng OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AxBits OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngZ OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngHeap OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngNtfM OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngWb OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AxTry OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngHeap.AxTry2 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_as1 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_ag0 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_ag1 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_taez.AXF_mmrz OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_taez.AXF_mmbz OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_ag1.AXF_aiz OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_ag1.AXF_ai0z OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_ag1.AXF_ins1z OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_taez.AXF_ins2z OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_taez.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

(* [comment removed for export] *)
Definition mp_ai (m : word -> option byte) (mt len ctr : Z) : word -> option byte :=
  wbytes (wbytes m (wa (mt + 32)) (word_to_le_bytes 8 (wa len))) (wa (0 + 614116)) (word_to_le_bytes 4 (wa (ctr + 1))).

Definition mp_ins1 (m : word -> option byte) (a mt sc cnt aidx usage len : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes m (wa (8 * sc + 614568)) (word_to_le_bytes 8 (wa (cnt + usage))))
    (wa (mt + 24)) (word_to_le_bytes 4 (wa (2 ^ (aidx + 1) - 1)))) (wa (mt + 28)) (word_to_le_bytes 4 (wa ((2 ^ cnt - 1) - (2 ^ (aidx + 1) - 1)))))
    (wa (mt + 16)) (word_to_le_bytes 8 (wa a))) (wa (a + 0)) (word_to_le_bytes 8 (wa mt))) (wa (a + 8)) (word_to_le_bytes 1 (wa aidx)))
    (wa (mt + 32)) (word_to_le_bytes 8 (wa (64 * sc + cnt + len + 31))).

Definition mp_ins2 (m : word -> option byte) (mt sc aidx : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes m (wa (mt + 24)) (word_to_le_bytes 4 (wa (2 ^ (aidx + 1) - 2)))) (wa (mt + 0)) (word_to_le_bytes 8 (wa mt)))
    (wa (mt + 8)) (word_to_le_bytes 8 (wa mt))) (wa (8 * sc + 614184)) (word_to_le_bytes 8 (wa mt)).

Definition mp_mem (m : word -> option byte) (mt a len sc cnt aidx usage ctr : Z) : word -> option byte :=
  mp_ins2 (mp_ins1 (mp_ai m mt len ctr) a mt sc cnt aidx usage len) mt sc aidx.

Ltac side := cbn [length word_to_le_bytes Z_to_le_bytes]; (rewrite ?u_wa_small by lia); lia.

Lemma mp_mem_out : forall m mt a len sc cnt aidx usage ctr x, 0 <= x < 2^64 -> 0 <= sc <= 47 -> 0 <= mt -> mt + 40 <= 2^64 ->
  0 <= a -> a + 9 <= 2^64 ->
  ~ (mt <= x < mt + 40) -> ~ (614116 <= x < 614120) -> ~ (8 * sc + 614568 <= x < 8 * sc + 614576) ->
  ~ (8 * sc + 614184 <= x < 8 * sc + 614192) -> ~ (a <= x < a + 9) ->
  mp_mem m mt a len sc cnt aidx usage ctr (wa x) = m (wa x).
Proof.
  intros m mt a len sc cnt aidx usage ctr x Hx Hsc H1 H2 H3 H4 N1 N2 N3 N4 N5.
  unfold mp_mem, mp_ins2, mp_ins1, mp_ai. rewrite !MngWb.wbytes_out by side. reflexivity.
Qed.

Lemma mp_mem_grows : forall m mt a len sc cnt aidx usage ctr, mem_grows m (mp_mem m mt a len sc cnt aidx usage ctr).
Proof.
  intros. unfold mp_mem, mp_ins2, mp_ins1, mp_ai. repeat (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl.
Qed.

(* [comment removed for export] *)
Lemma ag_aidx_l : forall sc cnt, 16 <= class_size sc <= 4080 -> 1 <= cnt < 4080 / class_size sc -> ag_aidx sc cnt = cnt - 1.
Proof.
  intros sc cnt Hs Hc. unfold ag_aidx, UNIT. change (4096 - 16) with 4080.
  destruct (cnt - 1 <? 4080 / class_size sc - 1) eqn:E; [apply Z.ltb_lt in E | apply Z.ltb_ge in E; lia].
  destruct (cnt - 1 <? 0) eqn:E2; [apply Z.ltb_lt in E2; lia | reflexivity].
Qed.

Lemma ag_aidx_g : forall sc cnt, 16 <= class_size sc <= 4080 -> 4080 / class_size sc <= cnt -> ag_aidx sc cnt = 4080 / class_size sc - 1.
Proof.
  intros sc cnt Hs Hc. unfold ag_aidx, UNIT. change (4096 - 16) with 4080.
  assert (1 <= 4080 / class_size sc) by (apply Z.div_le_lower_bound; lia).
  destruct (cnt - 1 <? 4080 / class_size sc - 1) eqn:E; [apply Z.ltb_lt in E; lia|].
  destruct (4080 / class_size sc - 1 <? 0) eqn:E2; [apply Z.ltb_lt in E2; lia | reflexivity].
Qed.

Lemma ag_aidx_0 : forall sc cnt, 4080 < class_size sc -> 1 <= cnt -> ag_aidx sc cnt = 0.
Proof.
  intros sc cnt Hs Hc. unfold ag_aidx, UNIT. change (4096 - 16) with 4080.
  rewrite (Z.div_small 4080 (class_size sc)) by lia. change (0 - 1) with (-1).
  destruct (cnt - 1 <? -1) eqn:E; [apply Z.ltb_lt in E; lia|]. reflexivity.
Qed.

Lemma ag_aidx_range : forall sc cnt, 16 <= class_size sc -> 1 <= cnt <= 32 -> 0 <= ag_aidx sc cnt <= cnt - 1.
Proof.
  intros sc cnt Hs Hc. unfold ag_aidx, UNIT. change (4096 - 16) with 4080.
  destruct (cnt - 1 <? 4080 / class_size sc - 1) eqn:E; [apply Z.ltb_lt in E | apply Z.ltb_ge in E];
    (destruct (_ <? 0) eqn:E2; [apply Z.ltb_lt in E2 | apply Z.ltb_ge in E2]); lia.
Qed.

Lemma le4_ctr : forall ctr, word_to_le_bytes 4 (wa (ext_Z true 0 4 ctr + 1)) = word_to_le_bytes 4 (wa (ctr + 1)).
Proof.
  intros ctr. apply le_wa_eqm; [|lia]. change (8 * Z.of_nat 4) with 32. rewrite ext4_swrap.
  rewrite Zplus_mod, swrap32_mod, <- Zplus_mod. reflexivity.
Qed.

Lemma le4_av : forall av, word_to_le_bytes 4 (wa (ext_Z true 0 4 av + -1)) = word_to_le_bytes 4 (wa (av - 1)).
Proof.
  intros av. apply le_wa_eqm; [|lia]. change (8 * Z.of_nat 4) with 32. rewrite ext4_swrap.
  rewrite Zplus_mod, swrap32_mod, <- Zplus_mod. reflexivity.
Qed.

Lemma len_bits : forall len, 0 <= len < 2^52 -> len mod 4096 = 0 ->
  Z.lor ((Z.shiftr ((4503599627370496 * 0) mod 2^64) 52) mod 2^64) ((4096 * Z.shiftr len 12) mod 2^64) = len.
Proof.
  intros len H1 H2. change ((4503599627370496 * 0) mod 2^64) with 0. change ((Z.shiftr 0 52) mod 2^64) with 0. rewrite Z.lor_0_l.
  rewrite Z.shiftr_div_pow2 by lia. change (2^12) with 4096. pose proof (Z_div_mod_eq_full len 4096). rewrite Z.mod_small; lia.
Qed.

Lemma bits_len : forall sc cnt len, 0 <= len -> len mod 4096 = 0 ->
  ((64 * sc) + (cnt + (4096 * Z.shiftr len 12))) + 31 = 64 * sc + cnt + len + 31.
Proof.
  intros sc cnt len H1 H2. rewrite Z.shiftr_div_pow2 by lia. change (2^12) with 4096. pose proof (Z_div_mod_eq_full len 4096). lia.
Qed.

Lemma br_divu_z : forall (x : bv 64) v c cnt, bv_unsigned x = v -> 1 <= v -> 0 <= c < 2^64 -> 0 <= cnt < 2^64 ->
  (cnt mod 2^64 <? bv_unsigned (mul_div M_DIVU (Z_to_bv 64 c) x) mod 2^64) = (cnt <? c / v).
Proof.
  intros x v c cnt Hx Hv Hc Hn. rewrite (divu_lit x v c Hx Hv Hc). rewrite (Z.mod_small cnt) by lia.
  rewrite Z.mod_small; [reflexivity|]. split; [apply Z.div_pos; lia|]. apply (Z.le_lt_trans _ c); [apply Z.div_le_upper_bound; nia | lia].
Qed.

Definition hide (P : Prop) : Prop := P.

Section AG3P.
Context {fx : FPState}.

#[using="Type"] Theorem seg_mpost : forall R m rom sp0 sc req can ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 R0 mt a len cnt usage ctr,
  as_frame R0 m sp0 sc req can ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 ->
  getr R 2 = wa (sp0 + -144 + -64) -> getr R 10 = wa a -> getr R 16 = wa 0 -> getr R 22 = wa 614096 ->
  getr R 23 = wa (8 * sc + 614096) -> getr R 24 = wa (class_size sc) -> getr R 25 = wa cnt ->
  rdn SEGS m (wa (sp0 + -144 + -8)) 8 = Some (word_to_le_bytes 8 (wa 338336)) ->
  rdn SEGS m (wa (sp0 + -144 + -16)) 8 = Some (word_to_le_bytes 8 (wa sc)) ->
  rdn SEGS m (wa (sp0 + -144 + -24)) 8 = Some (word_to_le_bytes 8 (wa mt)) ->
  rdn SEGS m (wa (sp0 + -144 + -32)) 8 = Some (word_to_le_bytes 8 (wa 18446744073709551615)) ->
  rdn SEGS m (wa (sp0 + -144 + -40)) 8 = Some (word_to_le_bytes 8 (wa len)) ->
  rdn SEGS m (wa (sp0 + -144 + -48)) 8 = Some (word_to_le_bytes 8 (wa 613952)) ->
  rdn SEGS m (wa (sp0 + -144 + -56)) 8 = Some (word_to_le_bytes 8 (wa (8 * sc + 614184))) ->
  4096 <= a -> a mod 4096 = 0 -> 4096 <= len <= 2^40 -> len mod 4096 = 0 -> a + len <= 2^47 ->
  1 <= mt <= 2^63-1 -> mt mod 8 = 0 -> 1 <= cnt <= 32 -> 0 <= usage <= 2^60 -> 0 <= ctr <= 2^32-1 ->
  rdn SEGS m (wa (mt + 32)) 8 = Some (word_to_le_bytes 8 (wa 0)) ->
  rdn SEGS m (wa (mt + 0)) 8 = Some (word_to_le_bytes 8 (wa 0)) ->
  rdn SEGS m (wa (mt + 8)) 8 = Some (word_to_le_bytes 8 (wa 0)) ->
  rdn SEGS m (wa (0 + 614116)) 4 = Some (word_to_le_bytes 4 (wa ctr)) ->
  rdn SEGS m (wa (8 * sc + 614568)) 8 = Some (word_to_le_bytes 8 (wa usage)) ->
  rdn SEGS m (wa (8 * sc + 614184)) 8 = Some (word_to_le_bytes 8 (wa 0)) ->
  rdn SEGS m (wa (a + 8)) 1 = Some (word_to_le_bytes 1 (wa 0)) ->
  (forall d k, 0 <= d -> d + Z.of_nat k <= 40 -> store_ok SEGS m (wa (mt + 0 + d)) k = true) ->
  (forall d k, 0 <= d -> d + Z.of_nat k <= 4 -> store_ok SEGS m (wa (0 + 614116 + d)) k = true) ->
  (forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (8 * sc + 614568 + d)) k = true) ->
  (forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (8 * sc + 614184 + d)) k = true) ->
  (forall d k, 0 <= d -> d + Z.of_nat k <= 9 -> store_ok SEGS m (wa (a + 0 + d)) k = true) ->
  (mt + 40 <= 0x10000 \/ 0x97000 <= mt) -> (a + len <= 0x10000 \/ 0x97000 <= a) -> (mt + 40 <= a \/ a + len <= mt) ->
  mt + 40 <= sp0 - 1024 -> a + len <= sp0 - 1024 -> 2^20 + 1024 <= sp0 ->
  exists R', msteps SEGS (mkst R (wa 0x533f0) m rom) (mkst R' (wa 0x52b8c) (mp_mem m mt a len sc cnt (ag_aidx sc cnt) usage ctr) rom) /\
    getr R' 1 = wa ra /\ getr R' 2 = wa sp0 /\ getr R' 8 = wa s0 /\ getr R' 9 = wa s1 /\ getr R' 10 = wa 0 /\
    getr R' 18 = wa s2 /\ getr R' 19 = wa s3 /\ getr R' 20 = wa s4 /\ getr R' 21 = wa s5 /\ getr R' 22 = wa s6 /\
    getr R' 23 = wa s7 /\ getr R' 24 = wa s8 /\ getr R' 25 = wa s9 /\
    (forall k, In k [3; 4; 26; 27]%nat -> getr R' (Z_to_bv 5 (Z.of_nat k)) = getr R (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros R m rom sp0 sc req can ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 R0 mt a len cnt usage ctr F
    R2 R10 R16 R22 R23 R24 R25 Mf1 Mf2 Mf3 Mf4 Mf5 Mf6 Mf7 Ha Hal Hlen Hlm Ha47 Hmt Amt Hcnt Hu Hctr
    Mw Mp Mn Mctr Musg Mact Mhb Wmt Wctr Wusg Wact Wa Dmt Da Dma Smt Sa Hsp'.
  pose proof F as [_ _ _ _ _ _ _ Hsp Asp Hsc Hreq Hcan Hra Hs0 Hs1 Hs2 Hs3 Hs4 Hs5 Hs6 Hs7 Hs8 Hs9
                   Fra Fs0 Fs1 Fs2 Fs3 Fs4 Fs5 Fs6 Fs7 Fs8 Fs9 Fcan Fgd].
  pose proof (size_classes_range sc ltac:(clear - Hsc; lia)) as Hun. pose proof (class_units sc) as Ecs.
  assert (Hsize : 16 <= class_size sc <= 131056) by (rewrite Ecs; clear - Hun; lia).
  (* [comment removed for export] *)
  assert (DA : forall x n, 0 <= n -> x + n <= 615032 -> 613952 <= x -> x + n <= mt \/ mt + 40 <= x) by (clear - Dmt; intros; lia).
  assert (DB : forall x n, 0 <= n -> x + n <= 615032 -> 613952 <= x -> x + n <= a \/ a + len <= x) by (clear - Da; intros; lia).
  assert (DC : mt + 40 <= a \/ a + len <= mt) by exact Dma.
  change (hide (mt + 40 <= 0x10000 \/ 0x97000 <= mt)) in Dmt. change (hide (a + len <= 0x10000 \/ 0x97000 <= a)) in Da.
  change (hide (mt + 40 <= a \/ a + len <= mt)) in Dma.
  (* [comment removed for export] *)
  assert (P1 : mmr_pre R m (sp0 + -144) a 0 sc mt 18446744073709551615 len 613952 (8 * sc + 614184)).
  { constructor; try assumption; clear - Hsp Hsp' Asp Ha Ha47 Hlen Hmt Hsc; lia. }
  destruct (mmr_pmr R m rom (sp0 + -144) a 0 sc mt 18446744073709551615 len 613952 (8 * sc + 614184) P1 ltac:(constructor))
    as (Ra & Hms1 & A1 & A2 & A8 & A9 & A10 & _ & A16 & A18 & A19 & A20 & A21 & AK).
  unfold mmr_mem_pmr in Hms1. clear P1.
  (* [comment removed for export] *)
  assert (P2 : mmb_pre Ra m a) by (constructor; [exact A10 | exact A18 | clear - Ha Ha47 Hlen; lia]).
  destruct (mmb_pmmb Ra m rom a P2 ltac:(constructor)) as (Rb & Hms2 & B10 & B18 & BK).
  unfold mmb_mem_pmmb in Hms2. clear P2.
  assert (B9 : getr Rb 9 = wa mt) by (regk BK 9%nat; exact A9).
  assert (B19 : getr Rb 19 = wa len) by (regk BK 19%nat; exact A19).
  assert (B22 : getr Rb 22 = wa 614096) by (regk BK 22%nat; regk AK 22%nat; exact R22).
  assert (B24 : getr Rb 24 = wa (class_size sc)) by (regk BK 24%nat; regk AK 24%nat; exact R24).
  assert (B25 : getr Rb 25 = wa cnt) by (regk BK 25%nat; regk AK 25%nat; exact R25).
  assert (Dmc : mt + 32 + 8 <= 0 + 614116 \/ 0 + 614116 + 4 <= mt + 32) by (pose proof (DA 614116 4); clear - H; lia).
  assert (Wm32 : forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (mt + 32 + d)) k = true).
  { intros d k Hd Hk. replace (mt + 32 + d) with (mt + 0 + (32 + d)) by ring. apply Wmt; clear - Hd Hk; lia. }
  (* [comment removed for export] *)
  set (aidx := ag_aidx sc cnt).
  assert (Hai : 0 <= aidx <= cnt - 1) by (apply ag_aidx_range; clear - Hsize Hcnt; lia).
  assert (AI : exists Rc, msteps SEGS (mkst Rb (wa 0x529a4) m rom) (mkst Rc (wa 0x529f8) (mp_ai m mt len ctr) rom) /\
                 getr Rc 9 = wa mt /\ getr Rc 10 = wa a /\ getr Rc 11 = wa (cnt + -1) /\ getr Rc 12 = wa aidx /\ getr Rc 25 = wa cnt /\
                 (forall k, In k [1; 2; 3; 4; 5; 6; 7; 8; 15; 16; 17; 20; 21; 23; 26; 27; 28; 29; 30; 31]%nat ->
                    getr Rc (Z_to_bv 5 (Z.of_nat k)) = getr Rb (Z_to_bv 5 (Z.of_nat k)))).
  { assert (EM : word_to_le_bytes 8 (wa (Z.lor ((Z.shiftr (((4503599627370496 * 0)) mod 2^64) 52) mod 2^64) (((4096 * Z.shiftr len 12)) mod 2^64))) =
                              word_to_le_bytes 8 (wa len)) by (rewrite len_bits by (clear - Hlen Hlm; lia); reflexivity).
    assert (Ram : 4096 <= a <= 2^47) by (clear - Ha Ha47 Hlen; lia).
    assert (Rln : 4096 <= len <= 2^40) by exact Hlen.
    destruct (Z_le_gt_dec (class_size sc) 4080) as [S1|S1].
    - assert (P : ai_pre Rb m a mt len (class_size sc) cnt ctr 0).
      { constructor; try assumption; clear - Hmt Hcnt Hctr S1 Hsize; lia. }
      destruct (Z_lt_ge_dec cnt (4080 / class_size sc)) as [C|C].
      + destruct (ai_pail Rb m rom a mt len (class_size sc) cnt ctr 0 P) as (Rc & Hms & C9 & C10 & C11 & C12 & _ & _ & _ & _ & _ & _ & C25 & CK).
        { scs_go; zats. rewrite (br_divu_z _ (class_size sc) 4080 cnt) by (first [apply zatom; [reflexivity | reflexivity | clear - Hsize; lia] | clear - Hsize Hcnt; lia]).
          apply Z.ltb_lt. exact C. }
        exists Rc. split; [|split; [exact C9 | split; [exact C10 | split; [exact C11 | split; [|split; [exact C25 | exact CK]]]]]].
        * unfold ai_mem_pail in Hms. rewrite EM, le4_ctr in Hms. exact Hms.
        * rewrite C12. unfold aidx. rewrite ag_aidx_l by (clear - Hsize S1 C Hcnt; lia). reflexivity.
      + destruct (ai_paig Rb m rom a mt len (class_size sc) cnt ctr 0 P) as (Rc & Hms & C9 & C10 & C11 & C12 & _ & _ & _ & _ & _ & _ & C25 & CK).
        { scs_go; zats. rewrite (br_divu_z _ (class_size sc) 4080 cnt) by (first [apply zatom; [reflexivity | reflexivity | clear - Hsize; lia] | clear - Hsize Hcnt; lia]).
          apply Z.ltb_ge. clear - C. lia. }
        exists Rc. split; [|split; [exact C9 | split; [exact C10 | split; [exact C11 | split; [|split; [exact C25 | exact CK]]]]]].
        * unfold ai_mem_paig in Hms. rewrite EM, le4_ctr in Hms. exact Hms.
        * rewrite C12. unfold aidx. rewrite ag_aidx_g by (clear - Hsize S1 C; lia). reflexivity.
    - assert (P : ai0_pre Rb m a mt len (class_size sc) cnt ctr 0).
      { constructor; try assumption; clear - Hmt Hcnt Hctr S1 Hsize; lia. }
      destruct (ai0_pai0 Rb m rom a mt len (class_size sc) cnt ctr 0 P) as (Rc & Hms & C9 & C10 & C11 & C12 & _ & _ & _ & _ & _ & _ & C25 & CK).
      { scs_go; zats. rewrite (br_divu_z _ (class_size sc) 4080 cnt) by (first [apply zatom; [reflexivity | reflexivity | clear - Hsize; lia] | clear - Hsize Hcnt; lia]).
        rewrite (Z.div_small 4080 (class_size sc)) by (clear - S1; lia). apply Z.ltb_ge. clear - Hcnt; lia. }
      exists Rc. split; [|split; [exact C9 | split; [exact C10 | split; [exact C11 | split; [|split; [exact C25 | exact CK]]]]]].
      * unfold ai0_mem_pai0 in Hms. rewrite EM, le4_ctr in Hms. exact Hms.
      * rewrite C12. unfold aidx. rewrite ag_aidx_0 by (clear - S1 Hcnt; lia). reflexivity. }
  destruct AI as (Rc & Hms3 & C9 & C10 & C11 & C12 & C25 & CK).
  (* [comment removed for export] *)
  assert (M1w : rdn SEGS (mp_ai m mt len ctr) (wa (mt + 32)) 8 = Some (word_to_le_bytes 8 (wa len))).
  { unfold mp_ai. rewrite (rdn_frame_n (wbytes m (wa (mt + 32)) (word_to_le_bytes 8 (wa len))) _ (mt + 32) 8) by
      (first [clear - Hmt; lia | intros x Hx; cbn [Z.of_nat Pos.of_succ_nat] in Hx; rewrite MngWb.wbytes_out by (clear - Hx Hmt Dmc; side); reflexivity]).
    apply rdn_wbytes_hit8. rewrite u_wa_small by (clear - Hmt; lia). clear - Hmt; lia. }
  assert (Fr1 : forall x n, 0 <= x -> x + Z.of_nat n <= 2^64 -> (x + Z.of_nat n <= mt + 32 \/ mt + 40 <= x) ->
                  (x + Z.of_nat n <= 614116 \/ 614120 <= x) -> rdn SEGS (mp_ai m mt len ctr) (wa x) n = rdn SEGS m (wa x) n).
  { intros x n H1 H2 H3 H4. apply rdn_frame_n; [exact H1 | exact H2 |]. intros y Hy. unfold mp_ai. rewrite !MngWb.wbytes_out by (clear - Hy H1 H2 H3 H4 Hmt; side). reflexivity. }
  assert (G1 : mem_grows m (mp_ai m mt len ctr)) by (unfold mp_ai; do 2 (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl).
  (* [comment removed for export] *)
  assert (P4 : ins1_pre Rc (mp_ai m mt len ctr) a mt sc cnt aidx usage len 0).
  { constructor.
    - regk CK 8%nat. regk BK 8%nat. exact A8.
    - exact C9.
    - exact C10.
    - exact C11.
    - exact C12.
    - regk CK 21%nat. regk BK 21%nat. exact A21.
    - regk CK 23%nat. regk BK 23%nat. regk AK 23%nat. exact R23.
    - exact C25.
    - clear - Ha Ha47 Hlen; lia.
    - exact Hmt.
    - exact Hsc.
    - exact Hcnt.
    - clear - Hai Hcnt; lia.
    - exact Hu.
    - clear - Hlen; lia.
    - clear; lia.
    - clear - Hal. apply Z.mod_divide in Hal; [|lia]. destruct Hal as (k & ->). replace (k * 4096) with ((k * 256) * 16) by ring. apply Z.mod_mul. lia.
    - exact Amt.
    - rewrite Fr1 by (pose proof (DA (8 * sc + 614568) 8); clear - H Hsc; lia). exact Musg.
    - exact M1w.
    - rewrite Fr1 by (pose proof (DB 614116 4); clear - H DC Ha Ha47 Hlen; cbn [Z.of_nat Pos.of_succ_nat]; lia). exact Mhb.
    - rewrite Fr1 by (pose proof (DA (8 * sc + 614184) 8); clear - H Hsc; lia). exact Mact.
    - rewrite Fr1 by (pose proof (DA 614116 4); clear - H Hmt; lia). exact Mp.
    - rewrite Fr1 by (pose proof (DA 614116 4); clear - H Hmt; lia). exact Mn.
    - intros d k Hd Hk. apply (store_ok_mono SEGS k m _ _ G1). exact (Wusg d k Hd Hk).
    - intros d k Hd Hk. apply (store_ok_mono SEGS k m _ _ G1). exact (Wmt d k Hd Hk).
    - intros d k Hd Hk. apply (store_ok_mono SEGS k m _ _ G1). exact (Wa d k Hd Hk).
    - intros d k Hd Hk. apply (store_ok_mono SEGS k m _ _ G1). exact (Wact d k Hd Hk).
    - pose proof (DA (8 * sc + 614568) 8); clear - H Hsc; lia.
    - pose proof (DB (8 * sc + 614568) 8); clear - H Hsc Hlen; lia.
    - clear - DC Hlen; lia.
    - pose proof (DA (8 * sc + 614184) 8); clear - H Hsc; lia.
    - pose proof (DB (8 * sc + 614184) 8); clear - H Hsc Hlen; lia.
    - clear; lia. }
  destruct (ins1_pins1 Rc (mp_ai m mt len ctr) rom a mt sc cnt aidx usage len 0 P4 ltac:(constructor))
    as (Rd & Hms4 & D8 & D9 & D10 & D11 & D12 & D13 & D21 & D23 & D25 & DK).
  clear P4.
  assert (EM1 : ins1_mem_pins1 (mp_ai m mt len ctr) Rc a mt sc cnt aidx usage len 0 = mp_ins1 (mp_ai m mt len ctr) a mt sc cnt aidx usage len).
  { unfold ins1_mem_pins1, mp_ins1. rewrite bits_len by (clear - Hlen Hlm; lia). change (Z.shiftr 0 5) with 0. rewrite Z.mul_0_r, !Z.add_0_r. reflexivity. }
  rewrite EM1 in Hms4. clear EM1.
  assert (G2 : mem_grows (mp_ai m mt len ctr) (mp_ins1 (mp_ai m mt len ctr) a mt sc cnt aidx usage len))
    by (unfold mp_ins1; do 7 (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl).
  (* [comment removed for export] *)
  assert (Hav : 1 <= 2 ^ (aidx + 1) - 1 <= 2^32-1).
  { assert (2 <= 2 ^ (aidx + 1)) by (change 2 with (2^1) at 1; apply Z.pow_le_mono_r; clear - Hai; lia).
    assert (2 ^ (aidx + 1) <= 2^32) by (apply Z.pow_le_mono_r; clear - Hai Hcnt; lia). clear - H H0; lia. }
  assert (M2av : rdn SEGS (mp_ins1 (mp_ai m mt len ctr) a mt sc cnt aidx usage len) (wa (mt + 24)) 4 = Some (word_to_le_bytes 4 (wa (2 ^ (aidx + 1) - 1)))).
  { unfold mp_ins1. rewrite (rdn_frame_n (wbytes (wbytes (mp_ai m mt len ctr) (wa (8 * sc + 614568)) (word_to_le_bytes 8 (wa (cnt + usage))))
                                  (wa (mt + 24)) (word_to_le_bytes 4 (wa (2 ^ (aidx + 1) - 1)))) _ (mt + 24) 4) by
      (first [clear - Hmt; lia | intros x Hx; cbn [Z.of_nat Pos.of_succ_nat] in Hx; rewrite !MngWb.wbytes_out by (clear - Hx Hmt DC Ha Hlen Ha47; side); reflexivity]).
    pose proof (rdn_wbytes_hit SEGS (word_to_le_bytes 4 (wa (2 ^ (aidx + 1) - 1))) (wbytes (mp_ai m mt len ctr) (wa (8 * sc + 614568)) (word_to_le_bytes 8 (wa (cnt + usage))))
                  (wa (mt + 24))) as H. rewrite length_N_to_le_bytes in H. apply H. rewrite u_wa_small by (clear - Hmt; lia). clear - Hmt; lia. }
  assert (Fr2 : forall x n, 0 <= x -> x + Z.of_nat n <= 2^64 -> (x + Z.of_nat n <= mt + 16 \/ mt + 40 <= x) ->
                  (x + Z.of_nat n <= 8 * sc + 614568 \/ 8 * sc + 614576 <= x) -> (x + Z.of_nat n <= a \/ a + 9 <= x) ->
                  (x + Z.of_nat n <= 614116 \/ 614120 <= x) ->
                  rdn SEGS (mp_ins1 (mp_ai m mt len ctr) a mt sc cnt aidx usage len) (wa x) n = rdn SEGS m (wa x) n).
  { intros x n H1 H2 H3 H4 H5 H6. assert (H3' : x + Z.of_nat n <= mt + 32 \/ mt + 40 <= x) by (clear - H3; lia).
    rewrite <- (Fr1 x n H1 H2 H3' H6). apply rdn_frame_n; [exact H1 | exact H2 |].
    intros y Hy. unfold mp_ins1. rewrite !MngWb.wbytes_out by (clear - Hy H1 H2 H3 H4 H5 Hmt Hsc Ha Hlen Ha47; side). reflexivity. }
  set (m2 := mp_ins1 (mp_ai m mt len ctr) a mt sc cnt aidx usage len) in *.
  assert (G12 : mem_grows m m2) by exact (mem_grows_trans _ _ _ G1 G2).
  assert (P5 : ins2_pre Rd m2 mt sc (2 ^ (aidx + 1) - 1)).
  { constructor.
    - exact D9.
    - exact D21.
    - exact Hmt.
    - exact Hsc.
    - exact Hav.
    - exact Amt.
    - exact M2av.
    - rewrite Fr2 by (pose proof (DA (8 * sc + 614184) 8); pose proof (DB (8 * sc + 614184) 8); clear - H H0 Hsc Hlen; lia). exact Mact.
    - rewrite Fr2 by (pose proof (DA 614116 4); pose proof (DA (8 * sc + 614568) 8); clear - H H0 Hsc Hmt DC Hlen; lia). exact Mp.
    - rewrite Fr2 by (pose proof (DA 614116 4); pose proof (DA (8 * sc + 614568) 8); clear - H H0 Hsc Hmt DC Hlen; lia). exact Mn.
    - intros d k Hd Hk. apply (store_ok_mono SEGS k m _ _ G12). exact (Wmt d k Hd Hk).
    - intros d k Hd Hk. apply (store_ok_mono SEGS k m _ _ G12). exact (Wact d k Hd Hk).
    - pose proof (DA (8 * sc + 614184) 8); clear - H Hsc; lia. }
  destruct (ins2_pins2 Rd m2 rom mt sc (2 ^ (aidx + 1) - 1) P5 ltac:(constructor)) as (Re & Hms5 & E9 & E10 & E21 & EK).
  clear P5.
  assert (EM2 : ins2_mem_pins2 m2 Rd mt sc (2 ^ (aidx + 1) - 1) = mp_ins2 m2 mt sc aidx).
  { unfold ins2_mem_pins2, mp_ins2. rewrite le4_av. replace (2 ^ (aidx + 1) - 1 - 1) with (2 ^ (aidx + 1) - 2) by ring. reflexivity. }
  rewrite EM2 in Hms5. clear EM2.
  change (mp_ins2 m2 mt sc aidx) with (mp_mem m mt a len sc cnt aidx usage ctr) in Hms5.
  (* [comment removed for export] *)
  assert (OUTF : forall x, sp0 - 96 <= x < sp0 \/ 613952 <= x < 613960 -> mp_mem m mt a len sc cnt aidx usage ctr (wa x) = m (wa x)).
  { intros x Hx. pose proof (DA 613952 8) as H1. pose proof (DB 613952 8) as H2.
    apply mp_mem_out; clear - Hx H1 H2 Hsp Hsp' Hsc Hmt Smt Sa Ha Hlen; lia. }
  assert (F' : as_frame R0 (mp_mem m mt a len sc cnt aidx usage ctr) sp0 sc req can ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9).
  { apply (as_frame_mem R0 m); [exact F | intros x Hx; apply OUTF; left; exact Hx | intros x Hx; apply OUTF; right; exact Hx]. }
  assert (P6 : tae_pre Re (mp_mem m mt a len sc cnt aidx usage ctr) can ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 sp0).
  { destruct F' as [_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Gra Gs0 Gs1 Gs2 Gs3 Gs4 Gs5 Gs6 Gs7 Gs8 Gs9 Gcan Ggd].
    constructor; try assumption.
    - regk EK 2%nat. regk DK 2%nat. regk CK 2%nat. regk BK 2%nat. exact A2.
    - regk EK 20%nat. regk DK 20%nat. regk CK 20%nat. regk BK 20%nat. exact A20. }
  destruct (tae_ptae Re _ rom can ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 sp0 P6 ltac:(constructor))
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
End AG3P.
