(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:528-543, 616-634;
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:41-45, 208-214, 230-234, for libreac/fuzz_identity's asan-ubsan build
   (lib/B). The same text also appears in projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:420-423, 430-444, 447-448,
   453-455, 470-475, 477-486, 489-491, 502-505, 511-514, 1255-1258. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_name_seg_rel.v, with its module paths, module names and numbers changed; 706 of its 765 lines of code are new or changed and 1865 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/on_announce_seg_tail.v, with its module names and numbers changed; 995 of its 1105 lines of code are new or changed and 655 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/on_announce_seg_sl2.v, with its module paths and module names changed; 498 of its 633 lines of code are new or changed and 970 lines of the source are left out. *)
(* on_announce_seg_dnb: the lemmas of the desk notice piece of on_announce's image-A walk (on_announce_seg_dn.v proves
   OnannCut.v onann_dn_stmt, code +0x308 .. +0x3f0 = 0x87d7c .. 0x87e64):
   - the symbolic states: ss_dn at the cut (+0x308; runs 1 and 2: n's shadow bytes 42 .. 50, n's first 44 bytes,
     g_s.notify / notify_ctx / state, their three shadow bytes, the spill slots sp1 + 8 .. sp1 + 32 and sp1 + 48 ..
     sp1 + 64; s5 = n is pinned to s2 + 336 and the alias s3 = (s2 >> 3) + SHADOW_OFF lets the check of the store at
     n + 24 read shadow byte 45), ss_dn3 after notice (+0x3d8: the slot sp1 + 32, the shadow byte of f + 30 and the
     byte at f + 30), ss_dnb at `bne a1, a2` (+0x3f0) with no region; their entry lemmas dn_entry, dn_entry3,
     dn_entryb;
   - the desk notice at n = F + 336 as notice's statement reads it (check_state_data_cg.v trans_ntc_at): dn_NB, its
     72 bytes from the run's chunks (dn_nb), dn_ntc_at, and notice_apart (dn_apart: an N_DESK notice writes GOT.desk,
     a byte of G, so neither a frame byte nor TF's, which onann_apart puts outside onann_wr);
   - the model: on_announce_m past the parse (dn_split), call_notify (dn_cn), the cmd byte (dn_cmd), the world fields
     at their numeral offsets, the ranges of off and of the personality pointer, g_fail_next and onann_ri across
     onann_w1 and set_GOT_desk;
   - values: the sign-extended state (dn_sext32), the zero-extended cmd byte (dn_zext8), `bne` on cmd and 0xe0. *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YN3v YI04 YI00 YI08 YG0s.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05 YImgTop.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c YO0f.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
DgnTransportSyms DgnTransportList DgnTransportAddr DgnTransportPa DgnTransportImg DgnTransportPaLib YC4b YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AE2k AE2y AsanCells TransportG AF0x.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
DgnTransportCg TransportGCg TransportGRwA TransportGRunA CanKit TransportGFrame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG TWorldA TImgA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import m_lost_cg check_state_data_cg notice_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import on_announce_cg OnannCut.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import session_lost_cg SlostCut SlostNtcKit SlostNtc.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import on_announce_seg_kit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require diginet_frame_parse_kit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require TransportGNotice.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TImg TSess0 TSess TCb TWorldLemmas TNeed.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require WalkNotify on_announce_lem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Mem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec DgnLib.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module FCells := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.AsanCells.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportG.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module TN := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TNeed.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module TSS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
Module DLib := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnLib.
Module LMem := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.Mem.
Module WN := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T.WalkNotify.
Module OAL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T.on_announce_lem.
Module FPK := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.diginet_frame_parse_kit.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* 1. The symbolic states                                              *)
(* ------------------------------------------------------------------ *)

(* The shadow byte of g_s.notify (s + 96); s + 104 and s + 112 have the next two. *)
Definition DN_SH : Z := 2148220740.
Lemma DN_SH_eq : DN_SH = SHADOW_OFF + (ONANN_S + 96) / 8 /\ DN_SH + 1 = SHADOW_OFF + (ONANN_S + 104) / 8 /\
  DN_SH + 2 = SHADOW_OFF + (ONANN_S + 112) / 8.
Proof. repeat split; reflexivity. Qed.

(* Runs 1 and 2 (+0x308 .. +0x3d4): n's shadow bytes 42 .. 50 (base s3, atom 19), n's first 44 bytes (base s2 = F,
   atom 18), g_s.notify / notify_ctx / state (atoms 32, 33, 34), their three shadow bytes (0), the slots sp1 + 8 ..
   sp1 + 32 (written) and sp1 + 48 .. sp1 + 64 (sp1 + 48 written, a = F + 256 read at sp1 + 56). *)
Definition DN_R_sh : YP09.region := YP09.mkRegion (Some 19%nat) 42 51 42 51 [].
Definition DN_R_n : YP09.region := YP09.mkRegion (Some 18%nat) 336 380 336 380 [].
Definition DN_R_gs : YP09.region :=
  YP09.mkRegion None (ONANN_S + 96) (ONANN_S + 116) 0 0
    [YP09.mkChunk (ONANN_S + 96) (YP09.CVal 8 (SOff 32 0)); YP09.mkChunk (ONANN_S + 104) (YP09.CVal 8 (SOff 33 0));
     YP09.mkChunk (ONANN_S + 112) (YP09.CVal 4 (SOff 34 0))].
Definition DN_R_shg : YP09.region :=
  YP09.mkRegion None DN_SH (DN_SH + 3) 0 0
    [YP09.mkChunk DN_SH (YP09.CVal 1 (SLit 0)); YP09.mkChunk (DN_SH + 1) (YP09.CVal 1 (SLit 0));
     YP09.mkChunk (DN_SH + 2) (YP09.CVal 1 (SLit 0))].
Definition DN_R_sl1 : YP09.region := YP09.mkRegion (Some 9%nat) 8 32 8 32 [].
Definition DN_R_sl2 : YP09.region :=
  YP09.mkRegion (Some 9%nat) 48 64 48 56 [YP09.mkChunk 56 (YP09.CVal 8 (SOff 18 256))].
Definition DN_RS : list YP09.region := [DN_R_sh; DN_R_n; DN_R_gs; DN_R_shg; DN_R_sl1; DN_R_sl2].
(* sp1 (atom 9) is 32-aligned in the stack; the frame F (atom 18) is 64-aligned; its first shadow byte s3 (atom 19) is
   (F >> 3) + SHADOW_OFF, 8-aligned. The run's static check asks a known range for each written region's base. *)
Definition DN_FACTS : facts :=
  mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (18%nat, mkAF 4096 (2 ^ 47) 6);
           (19%nat, mkAF (SHADOW_OFF + 512) (SHADOW_OFF + 2 ^ 44) 3)] []
    [(SAlu ALU_ADD (SAlu ALU_SRL (SOff 18 0) (SLit 3)) (SLit SHADOW_OFF), SOff 19 0)].
(* s4 = s, s8 = the shadow base, s5 = n = s2 + 336. *)
Definition DN_REGS : list sv :=
  sr_set (sr_set (sr_set sr_atoms (Z_to_bv 5 20) (SLit ONANN_S)) (Z_to_bv 5 24) (SLit SHADOW_OFF))
    (Z_to_bv 5 21) (SOff 18 336).
Definition ss_dn : sstate := mkSS ONANN_DN DN_REGS DN_RS None DN_FACTS.
Definition DN_Bx : sv := SLit 0.
Definition DN_B0 : Z * Z := (0, 0).

(* Run 3 (+0x3d8 .. +0x3f0, after notice): the slot sp1 + 32 (atom 32: the shadow byte's address of f + 30), that
   shadow byte (0), the byte at f + 30 (s11, atom 27; its value atom 33). s4 = s. *)
Definition DN_RET : Z := AF_on_announce + 0x3d8.
Definition DN3_R_sl : YP09.region := YP09.mkRegion (Some 9%nat) 32 40 0 0 [YP09.mkChunk 32 (YP09.CVal 8 (SOff 32 0))].
Definition DN3_R_fsh : YP09.region := YP09.mkRegion (Some 32%nat) 0 1 0 0 [YP09.mkChunk 0 (YP09.CVal 1 (SLit 0))].
Definition DN3_R_f30 : YP09.region := YP09.mkRegion (Some 27%nat) 0 1 0 0 [YP09.mkChunk 0 (YP09.CVal 1 (SOff 33 0))].
Definition ss_dn3 : sstate :=
  mkSS DN_RET (sr_set sr_atoms (Z_to_bv 5 20) (SLit ONANN_S)) [DN3_R_sl; DN3_R_fsh; DN3_R_f30] None (mkFacts [] [] []).

(* `bne a1, a2` (+0x3f0), taken up again from a state with no region. *)
Definition DN_BR : Z := AF_on_announce + 0x3f0.
Definition ss_dnb : sstate := mkSS DN_BR sr_atoms [] None (mkFacts [] [] []).

(* ------------------------------------------------------------------ *)
(* 2. Values                                                           *)
(* ------------------------------------------------------------------ *)

(* The sign-extended 4-byte load of an atom holding a u32: its signed value. *)
Lemma dn_sext32 : forall E (a : nat) u, ew E a = Z_to_bv 64 u -> 0 <= u < 2 ^ 32 ->
  sv_denot E (SExt true 32 (SOff a 0)) = Z_to_bv 64 (bv_swrap 32 u).
Proof.
  intros E a u H R. cbn [sv_denot]. rewrite H.
  rewrite unsigned_lit_small by lia. rewrite Z.add_0_r.
  rewrite LMem.sext_small, LMem.signed_of_extract by lia.
  rewrite unsigned_lit_small by lia. reflexivity.
Qed.

(* The zero-extended 1-byte load of an atom holding a byte. *)
Lemma dn_zext8 : forall E (a : nat) c, ew E a = Z_to_bv 64 c -> 0 <= c < 256 ->
  sv_denot E (SExt false 8 (SOff a 0)) = Z_to_bv 64 c.
Proof.
  intros E a c H R. cbn [sv_denot]. rewrite H.
  rewrite unsigned_lit_small by lia. rewrite Z.add_0_r.
  transitivity (Z_to_bv 64 (zext_low false 8 c)); [exact (zext_low_sound false 8 c)|].
  f_equal. unfold zext_low, zcanon, M64. cbv beta iota zeta. change (2 ^ Z.of_N 8) with 256.
  rewrite (Z.mod_small c (2 ^ 64)) by lia. rewrite (Z.mod_small c 256) by lia.
  apply Z.mod_small. lia.
Qed.

(* `bne` on two 64-bit values of bytes. *)
Lemma dn_eqb_byte : forall c d, 0 <= c < 256 -> 0 <= d < 256 -> bv_eqb (Z_to_bv 64 c) (Z_to_bv 64 d) = (c =? d).
Proof.
  intros c d Hc Hd. unfold bv_eqb. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  rewrite (Z.mod_small c (2 ^ 64)) by lia. rewrite (Z.mod_small d (2 ^ 64)) by lia. reflexivity.
Qed.

(* The alias of the state: s3 = (s2 >> 3) + SHADOW_OFF. *)
Lemma dn_alias : forall E F, ew E 18 = Z_to_bv 64 F -> ew E 19 = Z_to_bv 64 (SHADOW_OFF + F / 8) -> 0 <= F < 2 ^ 47 ->
  sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff 18 0) (SLit 3)) (SLit SHADOW_OFF)) = sv_denot E (SOff 19 0).
Proof.
  intros E F H18 H19 HF. pose proof (Z.div_pos F 8 ltac:(lia) ltac:(lia)) as HD0.
  pose proof (Z.div_le_upper_bound F 8 (2 ^ 44) ltac:(lia) ltac:(lia)) as HD1.
  apply U_inj. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw].
  rewrite !U_SOff, !U_SLit, H18, H19. unfold SHADOW_OFF in *.
  rewrite !unsigned_lit_small by lia. rewrite !Z.add_0_r.
  change (Z.land (zcanon 3) 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  rewrite (zcanon_id F) by (unfold M64; lia). rewrite (zcanon_id (F / 8)) by (unfold M64; lia).
  rewrite (zcanon_id 2147450880) by (unfold M64; lia). rewrite (zcanon_id (F / 8 + 2147450880)) by (unfold M64; lia).
  rewrite (zcanon_id (2147450880 + F / 8)) by (unfold M64; lia). lia.
Qed.

(* ------------------------------------------------------------------ *)
(* 3. The model                                                        *)
(* ------------------------------------------------------------------ *)

(* The world fields the code reads, at their numeral offsets. *)
Lemma dn_state_eq : forall Bx, TW.S_state Bx = bv_swrap 32 (TW.u_at Bx (TW.OFF_g_s + 112) 4).
Proof. intros Bx. reflexivity. Qed.
Lemma dn_notify_eq : forall Bx, TW.S_notify Bx = TW.u_at Bx (TW.OFF_g_s + 96) 8.
Proof. intros Bx. reflexivity. Qed.
Lemma dn_state_range : forall Bx, - 2 ^ 31 <= TW.S_state Bx < 2 ^ 31.
Proof. intros Bx. unfold TW.S_state. apply TWL.s32_range. Qed.

(* on_announce_m past the parse: the desk notice, then the arm of the cmd byte. *)
Lemma dn_split : forall (Fr : option TI.tframe) Bw b now Bw',
  onann_ign b = false -> TSS.on_announce_m timg_A Fr Bw b now = Some (Bw', tt) ->
  exists B2, TSS.call_notify timg_A Fr (onann_w1 timg_A Bw b) (onann_dntc timg_A (onann_w1 timg_A Bw b) b) =
      Some (B2, tt) /\
    (if DSpec.fr_cmd b =? TS0.DIGINET_CMD_ANNOUNCE then onann_k_e0 timg_A Fr B2 now
     else onann_k_e1 timg_A Fr B2 (onann_off (onann_w1 timg_A Bw b) b) b) = Some (Bw', tt).
Proof.
  intros Fr Bw b now Bw' Hig Hm. rewrite (onann_model_split timg_A Fr Bw b now Hig) in Hm.
  destruct (TSS.call_notify timg_A Fr (onann_w1 timg_A Bw b) (onann_dntc timg_A (onann_w1 timg_A Bw b) b))
    as [[B2 u]|]; [|discriminate Hm].
  destruct u. exists B2. split; [reflexivity | exact Hm].
Qed.

(* call_notify's test holds and notice_m gives its result. *)
Lemma dn_cn : forall (Fr : option TI.tframe) Bx n B2,
  TSS.call_notify timg_A Fr Bx n = Some (B2, tt) ->
  TW.S_notify Bx = TI.ti_notice timg_A /\ TC.notice_m timg_A Fr Bx n = Some (B2, tt).
Proof.
  intros Fr Bx n B2 H. unfold TSS.call_notify in H.
  destruct (Z.eqb_spec (TW.S_notify Bx) (TI.ti_notice timg_A)) as [E|E]; [|discriminate H].
  split; [exact E | exact H].
Qed.

(* The cmd byte of a frame the parse accepts is 0xe0 or 0xe1. *)
Lemma dn_cmd : forall b, onann_ign b = false ->
  DSpec.fr_cmd b = TS0.DIGINET_CMD_ANNOUNCE \/ DSpec.fr_cmd b = TS0.DIGINET_CMD_ANNOUNCE_SESSION.
Proof.
  intros b H. unfold onann_ign in H. apply negb_false_iff, Z.eqb_eq in H.
  change DLib.DIGINET_OK with 0 in H. exact (proj1 (OAL.oa_cmd_ok _ _ H)).
Qed.

Lemma dn_cmd_range : forall b, 0 <= DSpec.fr_cmd b < 256.
Proof. intros b. exact (OAL.oa_cmd_range b). Qed.

(* find_mac's result, and so off, is -1 .. 10. *)
Lemma dn_off_range : forall Bx b, -1 <= onann_off Bx b <= 10.
Proof.
  intros Bx b. unfold onann_off. destruct (DSpec.fr_cmd b =? TS0.DIGINET_CMD_ANNOUNCE_SESSION); [|lia].
  unfold TSS.find_mac_m. cbv beta. pose proof (OAL.oa_find_mac_range (DSpec.ann_unknown (DSpec.fr_body b))
    (TW.S_cfg_host_mac Bx) (Z.to_nat (15 - TS0.DIGINET_MAC_LEN + 1)) 0 ltac:(lia)) as R.
  change (Z.of_nat (Z.to_nat (15 - TS0.DIGINET_MAC_LEN + 1))) with 10 in R. lia.
Qed.

(* The personality pointer: 0 or an entry of timg_A's personalities. *)
Lemma dn_pv_range : forall b, 0 <= onann_pv timg_A b < 2 ^ 63.
Proof.
  intros b. unfold onann_pv. destruct (TN.diginet_personality_from_name (onann_name b)) as [i|] eqn:Ei; [|lia].
  destruct (OAL.oa_pfn_range _ _ Ei) as [-> | ->]; vm_compute; split; congruence.
Qed.

(* The two stores before the desk notice and the notice's GOT.desk keep the world's length, g_fail_next and the run
   invariants (1) and (4). *)
Lemma dn_len_upd : forall Bx k (v : list byte), length Bx = Z.to_nat TW.W_LEN -> 0 <= k ->
  k + Z.of_nat (length v) <= TW.W_LEN -> length (TW.upd Bx k v) = Z.to_nat TW.W_LEN.
Proof. intros Bx k v HL H1 H2. exact (OAL.oa_len_upd Bx v k HL H1 H2). Qed.

Lemma dn_ri_upd : forall Bx k (v : list byte), length Bx = Z.to_nat TW.W_LEN ->
  ((TW.OFF_g_s <= k /\ k + Z.of_nat (length v) <= TW.OFF_g_s + TW.SZ_g_s) \/
   (TW.OFF_GOT + 208 <= k /\ k + Z.of_nat (length v) <= TW.OFF_GOT + 212)) ->
  TW.g_fail_next (TW.upd Bx k v) = TW.g_fail_next Bx /\ (onann_ri Bx -> onann_ri (TW.upd Bx k v)).
Proof.
  intros Bx k v HL Hk. assert (LZ : Z.of_nat (length Bx) = TW.W_LEN) by (rewrite HL; unfold TW.W_LEN; lia).
  assert (LV : k + Z.of_nat (length v) <= Z.of_nat (length Bx))
    by (rewrite LZ; unfold TW.OFF_g_s, TW.SZ_g_s, TW.OFF_GOT, TW.W_LEN in *; lia).
  assert (K0 : 0 <= k) by (unfold TW.OFF_g_s, TW.OFF_GOT in *; lia).
  split.
  - unfold TW.g_fail_next. rewrite TWL.u_at_upd_out; [reflexivity | exact K0 | unfold TW.OFF_g_fail_next; lia | | exact LV].
    unfold TW.OFF_g_s, TW.SZ_g_s, TW.OFF_GOT, TW.OFF_g_fail_next in *. lia.
  - intros (R1 & R2 & R3).
    assert (EON : TW.M_fly_on (TW.upd Bx k v) = TW.M_fly_on Bx).
    { unfold TW.M_fly_on. rewrite TWL.s32_at_upd_out; [reflexivity | exact K0 | | | exact LV];
      unfold TW.A_M_fly_on, TW.OFF_g_s, TW.SZ_g_s, TW.OFF_GOT, TW.OFF_M in *; lia. }
    assert (ELN : TW.M_fly_len (TW.upd Bx k v) = TW.M_fly_len Bx).
    { unfold TW.M_fly_len. rewrite TWL.u_at_upd_out; [reflexivity | exact K0 | | | exact LV];
      unfold TW.A_M_fly_len, TW.OFF_g_s, TW.SZ_g_s, TW.OFF_GOT, TW.OFF_M in *; lia. }
    assert (ENC : TW.g_ncmd (TW.upd Bx k v) = TW.g_ncmd Bx).
    { unfold TW.g_ncmd. rewrite TWL.u_at_upd_out; [reflexivity | exact K0 | | | exact LV];
      unfold TW.OFF_g_ncmd, TW.OFF_g_s, TW.SZ_g_s, TW.OFF_GOT in *; lia. }
    assert (EST : forall s, 0 <= s -> TW.Cmd_st (TW.upd Bx k v) s = TW.Cmd_st Bx s).
    { intros s Hs. unfold TW.Cmd_st. rewrite TWL.s32_at_upd_out; [reflexivity | exact K0 | | | exact LV];
      unfold TW.A_Cmd_st, TW.OFF_g_s, TW.SZ_g_s, TW.OFF_GOT, TW.OFF_g_cmd in *; lia. }
    assert (ECL : forall s, 0 <= s -> TW.Cmd_len (TW.upd Bx k v) s = TW.Cmd_len Bx s).
    { intros s Hs. unfold TW.Cmd_len. rewrite TWL.u_at_upd_out; [reflexivity | exact K0 | | | exact LV];
      unfold TW.A_Cmd_len, TW.OFF_g_s, TW.SZ_g_s, TW.OFF_GOT, TW.OFF_g_cmd in *; lia. }
    split; [|split].
    + rewrite EON, ELN. exact R1.
    + intros s Hs Hp. rewrite ENC in Hs. rewrite (EST s ltac:(lia)) in Hp. rewrite (ECL s ltac:(lia)).
      exact (R2 s Hs Hp).
    + rewrite ENC. exact R3.
Qed.

(* onann_w1 is Bw or Bw with g_s.personality stored. *)
Lemma dn_w1 : forall Bw b, length Bw = Z.to_nat TW.W_LEN ->
  length (onann_w1 timg_A Bw b) = Z.to_nat TW.W_LEN /\
  TW.g_fail_next (onann_w1 timg_A Bw b) = TW.g_fail_next Bw /\
  (onann_ri Bw -> onann_ri (onann_w1 timg_A Bw b)).
Proof.
  intros Bw b HL. unfold onann_w1.
  destruct (TN.diginet_personality_from_name (onann_name b)); [|split; [exact HL | split; [reflexivity | tauto]]].
  unfold TW.set_S_personality.
  assert (LP : Z.of_nat (length (TW.put 8 (onann_pv timg_A b))) = 8) by (rewrite TWL.length_put; reflexivity).
  destruct (dn_ri_upd Bw TW.A_S_personality (TW.put 8 (onann_pv timg_A b)) HL
    ltac:(left; rewrite LP; unfold TW.A_S_personality, TW.OFF_g_s, TW.SZ_g_s; lia)) as [G R].
  split; [apply dn_len_upd; [exact HL | unfold TW.A_S_personality, TW.OFF_g_s; lia |
    rewrite LP; unfold TW.A_S_personality, TW.OFF_g_s, TW.W_LEN; lia]|].
  split; [exact G | exact R].
Qed.

Lemma dn_desk_ri : forall Bx d, length Bx = Z.to_nat TW.W_LEN ->
  TW.g_fail_next (TW.set_GOT_desk Bx d) = TW.g_fail_next Bx /\ (onann_ri Bx -> onann_ri (TW.set_GOT_desk Bx d)).
Proof.
  intros Bx d HL. unfold TW.set_GOT_desk. apply dn_ri_upd; [exact HL|]. right.
  rewrite TWL.length_put. unfold TW.A_GOT_desk. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* 4. The desk notice's bytes                                          *)
(* ------------------------------------------------------------------ *)

(* The 72 bytes the code stores at n (+0x334 .. +0x384) and the memset's 28 zeros (+0x394). *)
Definition dn_NB (st fpv ap pv off : Z) : list byte :=
  TW.put 4 1 ++ TW.put 4 st ++ TW.put 8 0 ++ TW.put 8 fpv ++ TW.put 8 ap ++ TW.put 8 pv ++ TW.put 4 off ++
  repeat (DSpec.b8 0) 28.

Lemma dn_NB_len : forall st fpv ap pv off, length (dn_NB st fpv ap pv off) = 72%nat.
Proof. intros. unfold dn_NB. rewrite !length_app, !TWL.length_put, repeat_length. reflexivity. Qed.

Lemma dn_nb : forall (H : word -> bool) (m : word -> option byte) p st fpv ap pv off,
  val_mem tfibsegs (mrestrict H m) p 4 1 ->
  val_mem tfibsegs (mrestrict H m) (p + 4) 4 st ->
  val_mem tfibsegs (mrestrict H m) (p + 8) 8 0 ->
  val_mem tfibsegs (mrestrict H m) (p + 16) 8 fpv ->
  val_mem tfibsegs (mrestrict H m) (p + 24) 8 ap ->
  val_mem tfibsegs (mrestrict H m) (p + 32) 8 pv ->
  val_mem tfibsegs (mrestrict H m) (p + 40) 4 off ->
  (forall a, p + 44 <= a < p + 72 -> aview tfibsegs H m a = Some 0) ->
  garr8 tfibsegs (mrestrict H m) p (map DSpec.bz (dn_NB st fpv ap pv off)).
Proof.
  intros H m p st fpv ap pv off V0 V4 V8 V16 V24 V32 V40 Z0.
  unfold dn_NB. rewrite !map_app.
  apply garr8_app. split; [exact (TransportGNotice.garr8_of_put tfibsegs _ _ 4 1 V0) |].
  rewrite length_map, TWL.length_put. change (p + Z.of_nat 4) with (p + 4).
  apply garr8_app. split; [exact (TransportGNotice.garr8_of_put tfibsegs _ _ 4 st V4) |].
  rewrite length_map, TWL.length_put. replace (p + 4 + Z.of_nat 4) with (p + 8) by lia.
  apply garr8_app. split; [exact (TransportGNotice.garr8_of_put tfibsegs _ _ 8 0 V8) |].
  rewrite length_map, TWL.length_put. replace (p + 8 + Z.of_nat 8) with (p + 16) by lia.
  apply garr8_app. split; [exact (TransportGNotice.garr8_of_put tfibsegs _ _ 8 fpv V16) |].
  rewrite length_map, TWL.length_put. replace (p + 16 + Z.of_nat 8) with (p + 24) by lia.
  apply garr8_app. split; [exact (TransportGNotice.garr8_of_put tfibsegs _ _ 8 ap V24) |].
  rewrite length_map, TWL.length_put. replace (p + 24 + Z.of_nat 8) with (p + 32) by lia.
  apply garr8_app. split; [exact (TransportGNotice.garr8_of_put tfibsegs _ _ 8 pv V32) |].
  rewrite length_map, TWL.length_put. replace (p + 32 + Z.of_nat 8) with (p + 40) by lia.
  apply garr8_app. split; [exact (TransportGNotice.garr8_of_put tfibsegs _ _ 4 off V40) |].
  rewrite length_map, TWL.length_put. replace (p + 40 + Z.of_nat 4) with (p + 44) by lia.
  rewrite map_repeat. change (DSpec.bz (DSpec.b8 0)) with 0.
  apply garr8_zeros. intros a Ha.
  pose proof (Z0 a ltac:(lia)) as Za. unfold aview in Za.
  destruct (YP09.mbyte tfibsegs (mrestrict H m) a) as [bb|] eqn:Eb; [|discriminate Za].
  cbn in Za. injection Za as Hb. f_equal. apply bv_eq. rewrite Hb. reflexivity.
Qed.

(* Two byte arrays at the same address of one memory are one array. *)
Lemma dn_garr8_eq : forall (H : word -> bool) (mm : word -> option byte) p (l1 l2 : list byte),
  garr8 tfibsegs (mrestrict H mm) p (map DSpec.bz l1) -> garr8 tfibsegs (mrestrict H mm) p (map DSpec.bz l2) ->
  length l1 = length l2 -> l1 = l2.
Proof.
  intros H mm p l1 l2 G1 G2 HL. apply (nth_ext l1 l2 (DSpec.b8 0) (DSpec.b8 0) HL). intros j Hj.
  pose proof (FPK.fp_garr8_aview H mm p _ j G1 ltac:(rewrite length_map; lia)) as A1.
  pose proof (FPK.fp_garr8_aview H mm p _ j G2 ltac:(rewrite length_map; lia)) as A2.
  rewrite A1 in A2. injection A2 as A2.
  rewrite (nth_indep _ 0 (DSpec.bz (DSpec.b8 0))) in A2 by (rewrite length_map; lia).
  rewrite (nth_indep (map DSpec.bz l2) 0 (DSpec.bz (DSpec.b8 0))) in A2 by (rewrite length_map; lia).
  rewrite !map_nth in A2. unfold DSpec.bz in A2. apply bv_eq. exact A2.
Qed.

(* The fields of the desk notice's bytes. *)
Lemma dn_NB_fields : forall st fpv ap pv off,
  - 2 ^ 31 <= st < 2 ^ 31 -> - 2 ^ 31 <= off < 2 ^ 31 -> 0 <= pv < 2 ^ 64 -> 0 <= ap < 2 ^ 64 ->
  let NB := dn_NB st fpv ap pv off in
  TW.s32_at NB 0 = 1 /\ TW.s32_at NB 4 = st /\ TW.s32_at NB 8 = 0 /\ TW.s32_at NB 12 = 0 /\
  TW.u_at NB 32 8 = pv /\ TW.s32_at NB 40 = off /\ TW.u_at NB 56 8 = 0 /\ TW.u_at NB 64 4 = 0 /\
  TW.u_at NB 68 2 = 0 /\ TW.u_at NB 48 8 = 0 /\ TW.u_at NB 24 8 = ap.
Proof.
  intros st fpv ap pv off Hst Hoff Hpv Hap. cbv zeta. unfold dn_NB.
  repeat split; OAL.oa_field.
Qed.

(* An announce field the notice reads has at most 10 bytes. *)
Lemma dn_ann_len : forall src, (length (TSS.ann_field src) <= 10)%nat.
Proof.
  intros src. unfold TSS.ann_field, DSpec.copy_len. rewrite length_app, length_firstn. cbn [length].
  pose proof (DSpec.nz_run_le (firstn (Nat.min 9 (10 - 1)) src)) as H. rewrite length_firstn in H. lia.
Qed.

(* A byte of the view is a stored byte. *)
Lemma dn_vm1 : forall (H : word -> bool) (m : word -> option byte) a v,
  aview tfibsegs H m a = Some v -> val_mem tfibsegs (mrestrict H m) a 1 v.
Proof.
  intros H m a v Hv.
  assert (R : 0 <= v < 256).
  { unfold aview in Hv. destruct (YP09.mbyte tfibsegs (mrestrict H m) a) as [bb|]; [|discriminate Hv].
    cbn in Hv. injection Hv as <-. pose proof (bv_unsigned_in_range 8 bb) as Hb.
    change (bv_modulus 8) with 256 in Hb. exact Hb. }
  assert (G : garr8 tfibsegs (mrestrict H m) a [v]).
  { apply FPK.fp_garr8_of_aview. intros j Hj. cbn [length] in Hj. assert (j = 0%nat) by lia. subst j.
    cbn [nth]. change (Z.of_nat 0) with 0. rewrite Z.add_0_r. split; [exact Hv | exact R]. }
  destruct (G 0%nat ltac:(cbn; lia)) as [V _]. cbn [nth] in V. change (Z.of_nat 0) with 0 in V.
  rewrite Z.add_0_r in V. exact V.
Qed.

(* ------------------------------------------------------------------ *)
(* 5. The entry states, the notice at n                                *)
(* ------------------------------------------------------------------ *)

Section k. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transport_listing PI_transport).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).

(* The valuation of runs 1 and 2: the registers at the cut, then g_s.notify, notify_ctx and state of W1. *)
Definition dn_vals (W1 : list byte) : list word :=
  [Z_to_bv 64 (TW.u_at W1 (TW.OFF_g_s + 96) 8); Z_to_bv 64 (TW.u_at W1 (TW.OFF_g_s + 104) 8);
   Z_to_bv 64 (TW.u_at W1 (TW.OFF_g_s + 112) 4)].
Definition dn_E (regs : bvmap 5 word) (W1 : list byte) : env := Eimg (PI := PI_transport) (Ereg regs (dn_vals W1)).

Lemma dn_entry0 : forall ly S (W : world segs) regs mem md W1 sp1 F,
  trans_onann_cells B -> @AR rc segs B ly S W mem md ->
  tw_at TMAP_A (aview segs (w_H W) mem) W1 ->
  YK11.getr regs 9 = w64 sp1 -> YK11.getr regs 18 = w64 F -> YK11.getr regs 19 = w64 (SHADOW_OFF + F / 8) ->
  4096 <= F -> F mod 64 = 0 -> in_app F 1024 ->
  (F + 1024 <= ONANN_S \/ ONANN_S + TW.SZ_g_s <= F) ->
  2 ^ 46 <= sp1 -> sp1 mod 32 = 0 -> F + 1024 <= sp1 -> sp1 + 64 <= 2 ^ 47 ->
  (forall a, F + 336 <= a < F + 380 -> apresent (w_H W) mem a) ->
  (forall i, 42 <= i < 51 -> apresent (w_H W) mem (SHADOW_OFF + F / 8 + i)) ->
  (forall a, sp1 + 8 <= a < sp1 + 56 -> apresent (w_H W) mem a) ->
  rdword (aview segs (w_H W) mem) (sp1 + 56) = Some (F + 256) ->
  st_ok_pi segs VAL (dn_E regs W1) (mkSS ONANN_DN sr_atoms DN_RS None DN_FACTS)
    (@YK11.mkst fx regs (Z_to_bv 64 (BASE + ONANN_DN)) (mrestrict (w_H W) mem) (YK11.seg_rom segs)).
Proof.
  intros ly S W regs mem md W1 sp1 F HZC HAR Htw R9 R18 R19 HF0 HF64 HFapp HFG Hsp Hsp32 Hsp2 Hsp3 Hpn Hpsh Hpsl S56.
  pose proof (Z.div_mod F 64 ltac:(lia)) as DF. rewrite HF64, Z.add_0_r in DF.
  assert (HF8 : F / 8 = 8 * (F / 64))
    by (rewrite DF at 1; replace (64 * (F / 64)) with ((8 * (F / 64)) * 8) by ring; apply Z.div_mul; lia).
  set (E := dn_E regs W1).
  assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = YK11.getr regs r)
    by (intros n r Hn; unfold E, dn_E; apply ew_Eimg_Ereg_nat; exact Hn).
  assert (U9 : bv_unsigned (ew E 9) = sp1)
    by (rewrite (EE 9%nat 9%bv eq_refl), R9; unfold w64; apply unsigned_lit_small; lia).
  assert (U18 : bv_unsigned (ew E 18) = F)
    by (rewrite (EE 18%nat 18%bv eq_refl), R18; unfold w64; apply unsigned_lit_small; lia).
  assert (U19 : bv_unsigned (ew E 19) = SHADOW_OFF + F / 8)
    by (rewrite (EE 19%nat 19%bv eq_refl), R19; unfold w64; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
  assert (EX : forall j, (j < 3)%nat -> ew E (32 + j) = nth j (dn_vals W1) (Z_to_bv 64 0))
    by (intros j Hj; unfold E, dn_E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
  pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33.
  pose proof (EX 2%nat ltac:(lia)) as E34.
  cbn [Nat.add nth dn_vals] in E32, E33, E34.
  pose proof (TWL.u_at_range W1 (TW.OFF_g_s + 96) 8) as R32.
  pose proof (TWL.u_at_range W1 (TW.OFF_g_s + 104) 8) as R33.
  pose proof (TWL.u_at_range W1 (TW.OFF_g_s + 112) 4) as R34.
  change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in R32, R33. change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in R34.
  assert (DEN : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff n 0) = Z_to_bv 64 v)
    by (intros n v Hn Hv; cbn [sv_denot]; rewrite Hn, unsigned_lit_small, Z.add_0_r by exact Hv; reflexivity).
  assert (ZSH : forall j, (j < 3)%nat -> val_mem segs (mrestrict (w_H W) mem) (DN_SH + Z.of_nat j) 1 0).
  { intros j Hj. apply AE2y.val_mem1_of_aview.
    replace (DN_SH + Z.of_nat j) with (FCells.shadow_addr (ONANN_S + 96 + 8 * Z.of_nat j)).
    - apply (decode_zshadow_rd B ly S W mem md ONANN_S (ONANN_S + TW.SZ_g_s) _ HAR); [| | | exact HZC].
      + unfold ONANN_S, TA_g_s. rewrite Z.add_mod, Z.mul_comm, Z.mod_mul by lia. reflexivity.
      + lia.
      + unfold TW.SZ_g_s. lia.
    - unfold FCells.shadow_addr, FCells.ASAN_K, DN_SH, ONANN_S, TA_g_s.
      replace (6158784 + 96 + 8 * Z.of_nat j) with ((769860 + Z.of_nat j) * 8) by lia.
      rewrite Z.div_mul by lia. lia. }
  apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - unfold DN_RS. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks DN_R_sh DN_R_n DN_R_gs DN_R_shg
        DN_R_sl1 DN_R_sl2 base_val]; rewrite ?U9, ?U18, ?U19.
    + split; [unfold SHADOW_OFF; lia|]. split; [unfold SHADOW_OFF; lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable segs). apply Hpsh. lia.
    + split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable segs). apply Hpn. lia.
    + split; [unfold ONANN_S, TA_g_s; lia|]. split; [unfold ONANN_S, TA_g_s; lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
      * apply (chunk_ok_val segs E _ 0 (ONANN_S + 96) 8 (SOff 32 0) (TW.u_at W1 (TW.OFF_g_s + 96) 8));
          [apply DEN; [exact E32 | exact R32] | exact R32 | lia |].
        replace (0 + (ONANN_S + 96)) with (TA_g_s + 96) by (unfold ONANN_S; lia).
        exact (tw_read_val segs _ TMAP_A W1 TW.OFF_g_s TA_g_s TW.SZ_g_s 96 8 TMAP_A_ok Htw TMAP_A_g_s
          ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)).
      * apply (chunk_ok_val segs E _ 0 (ONANN_S + 104) 8 (SOff 33 0) (TW.u_at W1 (TW.OFF_g_s + 104) 8));
          [apply DEN; [exact E33 | exact R33] | exact R33 | lia |].
        replace (0 + (ONANN_S + 104)) with (TA_g_s + 104) by (unfold ONANN_S; lia).
        exact (tw_read_val segs _ TMAP_A W1 TW.OFF_g_s TA_g_s TW.SZ_g_s 104 8 TMAP_A_ok Htw TMAP_A_g_s
          ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)).
      * apply (chunk_ok_val segs E _ 0 (ONANN_S + 112) 4 (SOff 34 0) (TW.u_at W1 (TW.OFF_g_s + 112) 4));
          [apply DEN; [exact E34 | lia] | exact R34 | lia |].
        replace (0 + (ONANN_S + 112)) with (TA_g_s + 112) by (unfold ONANN_S; lia).
        exact (tw_read_val segs _ TMAP_A W1 TW.OFF_g_s TA_g_s TW.SZ_g_s 112 4 TMAP_A_ok Htw TMAP_A_g_s
          ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)).
    + split; [unfold DN_SH; lia|]. split; [unfold DN_SH; lia|]. split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      * apply (chunk_ok_val segs E _ 0 DN_SH 1 (SLit 0) 0); [reflexivity | lia | lia |].
        rewrite Z.add_0_l. pose proof (ZSH 0%nat ltac:(lia)) as Z0. rewrite Z.add_0_r in Z0. exact Z0.
      * apply (chunk_ok_val segs E _ 0 (DN_SH + 1) 1 (SLit 0) 0); [reflexivity | lia | lia |].
        rewrite Z.add_0_l. exact (ZSH 1%nat ltac:(lia)).
      * apply (chunk_ok_val segs E _ 0 (DN_SH + 2) 1 (SLit 0) 0); [reflexivity | lia | lia |].
        rewrite Z.add_0_l. exact (ZSH 2%nat ltac:(lia)).
    + split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable segs). apply Hpsl. lia.
    + split; [lia|]. split; [lia|]. split.
      * intros o Ho. apply (apresent_writable segs). apply Hpsl. lia.
      * apply Forall_cons; [|apply Forall_nil].
        apply (chunk_ok_val segs E _ sp1 56 8 (SOff 18 256) (F + 256));
          [cbn [sv_denot]; rewrite U18; reflexivity | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | lia |].
        exact (val_mem_of_rdword segs (w_H W) mem _ _ S56).
  - apply pairwise_disjoint_of_extents.
    unfold DN_RS, extent_of_region, DN_R_sh, DN_R_n, DN_R_gs, DN_R_shg, DN_R_sl1, DN_R_sl2.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U18, U19.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, DN_SH, SHADOW_OFF, ONANN_S, TA_g_s, TW.SZ_g_s in *.
    rewrite HF8. repeat split; first [exact I | lia].
  - unfold DN_FACTS, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    refine (conj (conj _ (conj _ (conj _ I))) (conj I (conj _ I))).
    + unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U9. change (2 ^ 5) with 32. lia.
    + unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U18. change (2 ^ 6) with 64. lia.
    + unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U19. change (2 ^ 3) with 8.
      assert (M8 : (SHADOW_OFF + F / 8) mod 8 = 0).
      { rewrite HF8. unfold SHADOW_OFF. replace (2147450880 + 8 * (F / 64)) with ((268431360 + F / 64) * 8) by ring.
        apply Z.mod_mul. lia. }
      unfold SHADOW_OFF in *. lia.
    + apply (dn_alias E F); [rewrite (EE 18%nat 18%bv eq_refl); exact R18 | rewrite (EE 19%nat 19%bv eq_refl); exact R19 |].
      unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp. lia.
Qed.

Lemma dn_entry : forall ly S (W : world segs) regs mem md W1 sp1 F,
  trans_onann_cells B -> @AR rc segs B ly S W mem md ->
  tw_at TMAP_A (aview segs (w_H W) mem) W1 ->
  YK11.getr regs 9 = w64 sp1 -> YK11.getr regs 18 = w64 F -> YK11.getr regs 19 = w64 (SHADOW_OFF + F / 8) ->
  YK11.getr regs 20 = w64 ONANN_S -> YK11.getr regs 21 = w64 (F + ONANN_N) -> YK11.getr regs 24 = w64 SHADOW_OFF ->
  4096 <= F -> F mod 64 = 0 -> in_app F 1024 ->
  (F + 1024 <= ONANN_S \/ ONANN_S + TW.SZ_g_s <= F) ->
  2 ^ 46 <= sp1 -> sp1 mod 32 = 0 -> F + 1024 <= sp1 -> sp1 + 64 <= 2 ^ 47 ->
  (forall a, F + 336 <= a < F + 380 -> apresent (w_H W) mem a) ->
  (forall i, 42 <= i < 51 -> apresent (w_H W) mem (SHADOW_OFF + F / 8 + i)) ->
  (forall a, sp1 + 8 <= a < sp1 + 56 -> apresent (w_H W) mem a) ->
  rdword (aview segs (w_H W) mem) (sp1 + 56) = Some (F + 256) ->
  st_ok_pi segs VAL (dn_E regs W1) ss_dn
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + ONANN_DN)) mem (YK11.seg_rom segs))).
Proof.
  intros ly S W regs mem md W1 sp1 F HZC HAR Htw R9 R18 R19 R20 R21 R24 HF0 HF64 HFapp HFG Hsp Hsp32 Hsp2 Hsp3 Hpn
    Hpsh Hpsl S56.
  rewrite restrict_mkst_fx.
  pose proof (dn_entry0 ly S W regs mem md W1 sp1 F HZC HAR Htw R9 R18 R19 HF0 HF64 HFapp HFG Hsp Hsp32 Hsp2 Hsp3 Hpn
    Hpsh Hpsl S56) as H0.
  pose proof (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 20) ONANN_S H0 R20 eq_refl) as H1.
  pose proof (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 24) SHADOW_OFF H1 R24 eq_refl) as H2.
  assert (D21 : YK11.getr regs (Z_to_bv 5 21) = sv_denot (dn_E regs W1) (SOff 18 336)).
  { cbn [sv_denot]. unfold dn_E. rewrite (ew_Eimg_Ereg_nat regs (dn_vals W1) 18 18%bv eq_refl), R18. unfold w64.
    rewrite unsigned_lit_small by (unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp; lia).
    exact R21. }
  pose proof (st_ok_pi_set_reg _ _ _ (Z_to_bv 5 21) (SOff 18 336) H2
    ltac:(intros Hc; apply (f_equal bv_unsigned) in Hc; vm_compute in Hc; discriminate Hc) D21) as H3.
  exact H3.
Qed.

(* The state at +0x3d8, after notice: the registers as atoms, s4 = s; atoms 32 (the shadow byte's address of f + 30)
   and 33 (the byte at f + 30). *)
Definition dn_E3 (regs : bvmap 5 word) (fp cmd : Z) : env :=
  Eimg (PI := PI_transport) (Ereg regs [Z_to_bv 64 (SHADOW_OFF + (fp + 30) / 8); Z_to_bv 64 cmd]).

Lemma dn_entry3 : forall (W : world segs) regs mem sp1 fp cmd,
  YK11.getr regs 9 = w64 sp1 -> YK11.getr regs 27 = w64 (fp + 30) -> YK11.getr regs 20 = w64 ONANN_S ->
  2 ^ 46 <= sp1 -> sp1 + 64 <= 2 ^ 47 -> 4096 <= fp -> fp + 64 <= sp1 -> in_app fp 64 -> 0 <= cmd < 256 ->
  rdword (aview segs (w_H W) mem) (sp1 + 32) = Some (SHADOW_OFF + (fp + 30) / 8) ->
  aview segs (w_H W) mem (SHADOW_OFF + (fp + 30) / 8) = Some 0 ->
  aview segs (w_H W) mem (fp + 30) = Some cmd ->
  st_ok_pi segs VAL (dn_E3 regs fp cmd) ss_dn3
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + DN_RET)) mem (YK11.seg_rom segs))).
Proof.
  intros W regs mem sp1 fp cmd R9 R27 R20 Hsp Hsp2 Hfp0 Hfp Hfapp Hcmd S32 Vsh Vcmd.
  rewrite restrict_mkst_fx.
  set (E := dn_E3 regs fp cmd).
  assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = YK11.getr regs r)
    by (intros n r Hn; unfold E, dn_E3; apply ew_Eimg_Ereg_nat; exact Hn).
  assert (HSH : 0 <= (fp + 30) / 8 <= 2 ^ 44) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
  assert (U9 : bv_unsigned (ew E 9) = sp1)
    by (rewrite (EE 9%nat 9%bv eq_refl), R9; unfold w64; apply unsigned_lit_small; lia).
  assert (U27 : bv_unsigned (ew E 27) = fp + 30)
    by (rewrite (EE 27%nat 27%bv eq_refl), R27; unfold w64; apply unsigned_lit_small; lia).
  assert (E32 : ew E 32 = Z_to_bv 64 (SHADOW_OFF + (fp + 30) / 8))
    by (unfold E, dn_E3; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (E33 : ew E 33 = Z_to_bv 64 cmd)
    by (unfold E, dn_E3; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
  assert (U32 : bv_unsigned (ew E 32) = SHADOW_OFF + (fp + 30) / 8)
    by (rewrite E32; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
  assert (H0 : st_ok_pi segs VAL E (mkSS DN_RET sr_atoms [DN3_R_sl; DN3_R_fsh; DN3_R_f30] None (mkFacts [] [] []))
    (@YK11.mkst fx regs (Z_to_bv 64 (BASE + DN_RET)) (mrestrict (w_H W) mem) (YK11.seg_rom segs))).
  { apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
    - apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks DN3_R_sl DN3_R_fsh DN3_R_f30
          base_val]; rewrite ?U9, ?U27, ?U32.
      + split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        apply Forall_cons; [|apply Forall_nil].
        apply (chunk_ok_val segs E _ sp1 32 8 (SOff 32 0) (SHADOW_OFF + (fp + 30) / 8));
          [cbn [sv_denot]; rewrite U32, Z.add_0_r; reflexivity | unfold SHADOW_OFF; change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia
          | lia |].
        exact (val_mem_of_rdword segs (w_H W) mem _ _ S32).
      + split; [unfold SHADOW_OFF; lia|]. split; [unfold SHADOW_OFF; lia|]. split; [intros o Ho; lia|].
        apply Forall_cons; [|apply Forall_nil].
        apply (chunk_ok_val segs E _ (SHADOW_OFF + (fp + 30) / 8) 0 1 (SLit 0) 0); [reflexivity | lia | lia |].
        rewrite Z.add_0_r. exact (AE2y.val_mem1_of_aview _ _ _ _ Vsh).
      + split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        apply Forall_cons; [|apply Forall_nil].
        apply (chunk_ok_val segs E _ (fp + 30) 0 1 (SOff 33 0) cmd);
          [cbn [sv_denot]; rewrite E33, unsigned_lit_small, Z.add_0_r by lia; reflexivity
          | change (2 ^ (8 * Z.of_N 1)) with 256; lia | lia |].
        rewrite Z.add_0_r. exact (dn_vm1 _ _ _ _ Vcmd).
    - apply pairwise_disjoint_of_extents.
      unfold extent_of_region, DN3_R_sl, DN3_R_fsh, DN3_R_f30.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U27, U32.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *.
      repeat split; first [exact I | lia].
    - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. repeat split; exact I. }
  exact (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 20) ONANN_S H0 R20 eq_refl).
Qed.

(* The state at +0x3f0 with no region. *)
Lemma dn_entryb : forall (W : world segs) regs mem,
  st_ok_pi segs VAL (Eimg (PI := PI_transport) (Ereg regs [])) ss_dnb
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + DN_BR)) mem (YK11.seg_rom segs))).
Proof.
  intros W regs mem. rewrite restrict_mkst_fx. unfold ss_dnb.
  apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. exact I.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. repeat split; exact I.
Qed.

(* The desk notice at n = F + 336, as notice's statement reads it. *)
Lemma dn_ntc_at : forall lyc S2 (W : world segs) memN mdN (regsC : bvmap 5 word) W1 b F pos fpv,
  AR_laws segs B -> @AR rc segs B lyc S2 W memN mdN -> In (ONANN_CID, pos) (frames S2) ->
  frame_addr lyc ONANN_CID pos = F -> 4096 <= F -> F mod 64 = 0 -> F + 1024 <= alloc_ceiling -> in_app F 1024 ->
  F + 1024 <= spZ regsC - NOTICE_STK ->
  (forall i, 32 <= i < 37 -> aview segs (w_H W) memN (SHADOW_OFF + F / 8 + i) = Some 0) ->
  (forall i, 42 <= i < 51 -> aview segs (w_H W) memN (SHADOW_OFF + F / 8 + i) = Some 0) ->
  garr8 segs (mrestrict (w_H W) memN) (F + 336)
    (map DSpec.bz (dn_NB (TW.S_state W1) fpv (F + 256) (onann_pv timg_A b) (onann_off W1 b))) ->
  garr8 segs (mrestrict (w_H W) memN) (F + ONANN_A) (map DSpec.bz (TSS.ann_field (skipn 15 (DSpec.fr_body b)))) ->
  garr8 segs (mrestrict (w_H W) memN) (F + ONANN_A + 10)
    (map DSpec.bz (TSS.ann_field (skipn 24 (DSpec.fr_body b)))) ->
  trans_ntc_at B lyc S2 W memN regsC NOTICE_STK (F + 336) (onann_dntc timg_A W1 b).
Proof.
  intros lyc S2 W memN mdN regsC W1 b F pos fpv LAWS HAR Hin EF HF0 HF64 HFc HFapp Hwin ZSa ZSn HNB HV HN.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  destruct (al_frames _ _ LAWS lyc S2 W memN mdN ONANN_CID pos HAR Hin) as (_ & _ & HFb & HFsh).
  rewrite EF in HFb, HFsh. change (fs_frame_bytes ONANN_CID) with 1024 in HFb.
  change (fs_frame_bytes ONANN_CID / 8) with 128 in HFsh. change (shadow_addr F) with (SHADOW_OFF + F / 8) in HFsh.
  assert (DFm8 : F mod 8 = 0).
  { pose proof (Z.div_mod F 64 ltac:(lia)) as D. rewrite HF64, Z.add_0_r in D. rewrite D.
    replace (64 * (F / 64)) with ((8 * (F / 64)) * 8) by ring. apply Z.mod_mul. lia. }
  pose proof (dn_state_range W1) as Hst. pose proof (dn_off_range W1 b) as Hoff. pose proof (dn_pv_range b) as Hpv.
  destruct (dn_NB_fields (TW.S_state W1) fpv (F + 256) (onann_pv timg_A b) (onann_off W1 b) Hst ltac:(lia)
    ltac:(lia) ltac:(lia)) as (F0 & F4 & F8 & F12 & F32 & F40 & F56 & F64 & F68 & F48 & F24).
  assert (HRD : forall q n, F <= q -> q + n <= F + 1024 -> 1 <= n ->
    (forall i, q / 8 - F / 8 <= i < (q + n + 7) / 8 - F / 8 -> aview segs (w_H W) memN (SHADOW_OFF + F / 8 + i) = Some 0) ->
    decode_rd_ok W memN q n).
  { intros q n Hq1 Hq2 Hn ZS. unfold decode_rd_ok. split; [|split; [|split; [|split; [|split]]]].
    - intros a Ha. apply can_aview_vis. exact (proj1 (HFb a ltac:(lia))).
    - apply (TransportGNotice.frame_ra_zero _ F q n (q / 8 - F / 8) ((q + n + 7) / 8 - F / 8));
        [lia | exact DFm8 | | | exact ZS].
      + pose proof (Z.div_mod q 8 ltac:(lia)). pose proof (Z.mod_pos_bound q 8 ltac:(lia)).
        pose proof (Z.div_mod F 8 ltac:(lia)). lia.
      + pose proof (Z.div_mod (q + n + 7) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (q + n + 7) 8 ltac:(lia)).
        pose proof (Z.div_mod F 8 ltac:(lia)). lia.
    - apply (TransportGNotice.frame_hull_vis _ F 1024 q n); [lia | exact HF64 | reflexivity | lia | lia | lia |].
      intros i Hi. apply can_aview_vis. exact (proj1 (HFsh i Hi)).
    - apply (amem_range_sub_app F 1024); [exact HFapp | lia | lia | lia | lia].
    - lia.
    - unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp. lia. }
  assert (DIV : forall c, (F + c) / 8 = F / 8 + c / 8).
  { intros c. pose proof (Z.div_mod F 8 ltac:(lia)) as D8. rewrite DFm8, Z.add_0_r in D8.
    replace (F + c) with (F / 8 * 8 + c) by lia. apply Z.div_add_l. lia. }
  unfold trans_ntc_at.
  split; [lia|]. split; [rewrite Z.add_mod, DFm8 by lia; reflexivity|].
  split.
  { right. split.
    - left. exists ONANN_CID, pos. split; [exact Hin|]. rewrite EF. change (fs_frame_bytes ONANN_CID) with 1024.
      unfold NTC_SIZE. lia.
    - unfold NTC_SIZE. apply HRD; [lia | lia | lia |]. intros i Hi.
      rewrite (DIV 336) in Hi. replace (F + 336 + 72 + 7) with (F + 415) in Hi by lia. rewrite (DIV 415) in Hi.
      change (336 / 8) with 42 in Hi. change (415 / 8) with 51 in Hi.
      apply ZSn. lia. }
  split; [left; unfold NTC_SIZE; lia|].
  exists (dn_NB (TW.S_state W1) fpv (F + 256) (onann_pv timg_A b) (onann_off W1 b)).
  split; [exact HNB|]. split; [exact (dn_NB_len _ _ _ _ _)|].
  unfold onann_dntc. cbn [TI.n_kind TI.n_state TI.n_old TI.n_reason TI.n_pers TI.n_mac_offset TI.n_body_len TI.n_counter
    TI.n_retry TI.n_body TI.n_ann length].
  rewrite F48, F24.
  split; [rewrite F0; reflexivity|].
  split; [exact F4|]. split; [exact F8|]. split; [exact F12|]. split; [exact F32|]. split; [exact F40|].
  split; [exact F56|]. split; [exact F64|]. split; [exact F68|].
  split; [apply garr8_nil|]. split; [exact (trans_src_ok_null B lyc S2 W memN)|]. split; [left; lia|].
  unfold onann_ann. cbn [TI.ta_version TI.ta_name].
  split; [lia|]. split; [rewrite Z.add_mod, DFm8 by lia; reflexivity|].
  split; [exact HV|]. split; [exact HN|].
  split.
  { right. split.
    - left. exists ONANN_CID, pos. split; [exact Hin|]. rewrite EF. change (fs_frame_bytes ONANN_CID) with 1024.
      unfold ANN_SIZE. lia.
    - unfold ANN_SIZE. apply HRD; [lia | lia | lia |]. intros i Hi.
      rewrite (DIV 256) in Hi. replace (F + 256 + 20 + 7) with (F + 283) in Hi by lia. rewrite (DIV 283) in Hi.
      change (256 / 8) with 32 in Hi. change (283 / 8) with 35 in Hi.
      apply ZSa. lia. }
  left. unfold ANN_SIZE. lia.
Qed.

(* notice's stores (an N_DESK notice: GOT.desk, a byte of G) are apart from n's bytes and a's (frame bytes are not
   image bytes), from the empty body, and from TF (onann_apart: they are bytes of onann_wr). *)
Lemma dn_apart : forall lyc S2 (W2 : world segs) mem2 md2 (W : world segs) memN (TF : option TI.tframe) Bw b F pos
    (NB0 : list byte),
  AR_laws segs B -> @AR rc segs B lyc S2 W2 mem2 md2 -> In (ONANN_CID, pos) (frames S2) ->
  frame_addr lyc ONANN_CID pos = F -> onann_apart TF Bw b ->
  garr8 segs (mrestrict (w_H W) memN) (F + 336) (map DSpec.bz NB0) -> length NB0 = 72%nat ->
  TW.u_at NB0 24 8 = F + 256 ->
  notice_apart W memN (F + 336) (onann_dntc timg_A (onann_w1 timg_A Bw b) b) TF (onann_w1 timg_A Bw b).
Proof.
  intros lyc S2 W2 mem2 md2 W memN TF Bw b F pos NB0 LAWS HAR Hin EF Hap HNB0 HL0 H24 x Hx.
  assert (Hw : onann_wr Bw b x) by exact (onann_wr_dntc _ _ Bw b x Hx).
  assert (HxG : inG TG.G_HARNESS x) by exact (onann_wr_G Bw b x Hw).
  assert (NF : forall a, F <= a < F + 1024 -> a <> x).
  { intros a Ha ->. apply (frm_img segs B LAWS lyc S2 W2 mem2 md2 ONANN_CID pos x HAR Hin);
      [rewrite EF; change (fs_frame_bytes ONANN_CID) with 1024; lia | exact (trans_g_img x HxG)]. }
  split; [|split].
  - intros Hr. unfold NTC_SIZE in Hr. exact (NF x ltac:(lia) eq_refl).
  - intros NB HNB HL. rewrite (dn_garr8_eq _ _ _ NB NB0 HNB HNB0 ltac:(rewrite HL, HL0; reflexivity)).
    split.
    + unfold onann_dntc. cbn [TI.n_body length Z.of_nat]. lia.
    + intros _. rewrite H24. unfold ANN_SIZE. intros Hr. exact (NF x ltac:(lia) eq_refl).
  - intros fr Hfr. exact (Hap x Hw fr Hfr).
Qed.

End k.
