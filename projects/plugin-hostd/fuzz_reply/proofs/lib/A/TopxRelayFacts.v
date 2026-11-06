(* The instance facts of relay_remove's and relay_instance_gone's _x walks (lib/A/W_relay_remove.v Section c,
   pb_relay_remove_x; lib/A/W_relay_instance_gone.v Section c, pb_relay_instance_gone_x) at the instance of A's top
   step (lib/A/W_LLVMFuzzerTestOneInput_top_x.v): PI := PB_fr, B := TfibB, RG := fr_RG, PST := [], ARx := top_x's ARX
   (written out here as the same relation, as lib/A/TopxDrainLit.v does, so this file does not Require top_x).  Each
   lemma's type is the Section hypothesis text at that instance, so top_x passes it to the walk by eassumption:
     topx_rr_HG / topx_rr_HROMO     relay_remove's HG / HROMO: G_RR (W_contract.v) lies in G_fr_c, which gx_ok and
                                    rom_out hold of (lib/A/W_drain_pb.v gx_ok_incl / rom_out_incl over
                                    W_LLVMFuzzerTestOneInput_G.v c_gx_ok / c_rom_out; the lock and g_nsrc by c_HGlock /
                                    c_HGnsrc, the rest by c_HG_DR)
     topx_rig_HGRIG / topx_rig_HROMO  relay_instance_gone's HGRIG / HROMO, the same way over c_HG_RIG
     topx_HH59 / topx_HH60 / topx_HV4  relay_remove's register images of g_nsrc / g_src and g_wake[1], by vm_compute
     topx_HH44 / topx_HH45         relay_instance_gone's register images of g_nsrc / g_src, by vm_compute
     topx_HRGP                     both walks' HRGP (one text), by W_drain_pb.v zpairwise_disjb_ok and vm_compute
     topx_HRGI                     both walks' HRGI (one text): the four cells are G_fr_c objects (c_HG_smax /
                                    c_HG_client / c_HG_sdead, g_capsrc by rng_cover), so image bytes (c_img) and not
                                    owned (lib/A/W_LLVMFuzzerTestOneInput_addI.v zz_HOWN)
     topx_HEND5L                   both walks' HEND5L: " end\0" (A_OBJ 31 = 0x20f00) by TopxDrainLit.v's dlit_romb
     topx_HCANR                    relay_instance_gone's HCANR: the canary's 8 bytes at FR_GUARD = 0x5f94b0 read Some
                                    from the image (seg_rom), decided by vm_compute
     topx_HLIT20_x / topx_HLIT21_x / topx_HLIT31_x  relay_instance_gone's three glit_at_x literals ("%s %d \0" at
                                    A_OBJ 20 = 0x20f80, "param_gesture\0" at A_OBJ 21 = 0x20f20, " end\0" at A_OBJ 31):
                                    the bytes and in_rom by dlit_romb, the shadow by lib/A/W_shadow_pin_x.v (tfib_shp_x
                                    for A_OBJ 20 / 7 bytes, ashp_gesture_14_fr_x, ashp_end5_5_fr_x), the granule's tail
                                    bytes by vm_compute
   ARX's laws are TopxDrainLit.v's topx_dlit_ARX_laws (the proof of top_x's ARX_laws).
   proves no function (kind: segment lemma of LLVMFuzzerTestOneInput's top step). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YM05 YP0b YA0n YA0q YG00 YG0a YG01 YG0f YG0n YG0d YG0v YI04 YI00 YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YI16.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_syms W_listing W_place W_tbl W_kit W_img W_journal W_contract W_rep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_journal_x W_contract_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AD2l CfParamsReply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import CfImgA.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfNames YG0ncf YGcallcf YG0lawscf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_LLVMFuzzerTestOneInput_cut W_LLVMFuzzerTestOneInput_G.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require RelayModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require
W_sites AE2k W_shadow_pin_x W_LLVMFuzzerTestOneInput_addI TopxDrainLit W_drain_pb W_relay_remove_cx
W_relay_instance_gone_cx.
(* the zify flag as this file's proofs expect it, whatever a Required file leaves (TopxDrainLit.v's form) *)
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---- a range of image bytes that read Some from the image's own segments (seg_rom), decided over frsegs ---- *)
Definition rom_someb (lo n : Z) : bool :=
  forallb (fun j => match seg_rom frsegs (Z_to_bv 64 (lo + Z.of_nat j)) with Some _ => true | None => false end)
    (seq 0 (Z.to_nat n)).

Lemma rom_someb_ok : forall lo n, rom_someb lo n = true ->
  forall x, lo <= x < lo + n -> seg_rom frsegs (Z_to_bv 64 x) <> None.
Proof.
  intros lo n H x Hx. unfold rom_someb in H. rewrite forallb_forall in H.
  specialize (H (Z.to_nat (x - lo)) ltac:(apply in_seq; lia)). rewrite Z2Nat.id in H by lia.
  replace (lo + (x - lo)) with x in H by lia.
  destruct (seg_rom frsegs (Z_to_bv 64 x)); [discriminate | discriminate H].
Qed.

(* glit_at_x's fourth conjunct: the bytes after a literal's NUL to the end of its 8-byte granule *)
Lemma rom_tail_ok : forall base len,
  rom_someb (base + len) (base + len - 1 - (base + len - 1) mod 8 + 8 - (base + len)) = true ->
  forall x, base + len <= x < base + len - 1 - (base + len - 1) mod 8 + 8 -> seg_rom frsegs (Z_to_bv 64 x) <> None.
Proof. intros base len H x Hx. apply (rom_someb_ok _ _ H). lia. Qed.

Section topx_relay.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PB_fr).
(* top_x's Definition ARX, the same relation *)
#[local] Notation ARX := (fun ly S Hp (W : world segs) mem md =>
  ARcf (ci := CfImg_A) (cp := CfParams_reply) segs TfibB ly S Hp W mem md /\ Hp = []).
#[local] Existing Instance AE2k.tfib_sink_head.
#[local] Notation HEV := (W_LLVMFuzzerTestOneInput_addI.zz_HEV TfibB TfibB_syms).

(* ---- HG / HROMO (relay_remove) and HGRIG / HROMO (relay_instance_gone): their G lies in G_fr_c ---- *)
Lemma topx_rr_Gin : forall a, inG (G_RR TfibB fr_RG) a -> inG (G_fr_c TfibB) a.
Proof.
  intros a Ha. unfold G_RR in Ha.
  apply inG_cons in Ha as [Ha|Ha]; [unfold in_zr in Ha; cbn [fst snd] in Ha; exact (c_HGlock TfibB a Ha)|].
  apply inG_cons in Ha as [Ha|Ha]; [unfold in_zr in Ha; cbn [fst snd] in Ha; exact (c_HGnsrc TfibB a Ha)|].
  exact (c_HG_DR TfibB a Ha).
Qed.
Lemma topx_rr_HG : gx_ok segs TfibB (G_RR TfibB fr_RG).
Proof.
  apply (W_drain_pb.gx_ok_incl _ _ _ _ topx_rr_Gin).
  exact (c_gx_ok TfibB HEV (W_LLVMFuzzerTestOneInput_addI.zz_HOWN TfibB TfibB_syms)
    (W_LLVMFuzzerTestOneInput_addI.zz_HKEPT TfibB TfibB_syms)).
Qed.
Lemma topx_rr_HROMO : rom_out segs TfibB (G_RR TfibB fr_RG).
Proof.
  apply (W_drain_pb.rom_out_incl _ _ _ _ topx_rr_Gin).
  exact (c_rom_out TfibB TfibB_syms HEV).
Qed.
Lemma topx_rig_HGRIG : gx_ok segs TfibB (G_RIG TfibB fr_RG).
Proof.
  apply (W_drain_pb.gx_ok_incl _ _ _ _ (c_HG_RIG TfibB)).
  exact (c_gx_ok TfibB HEV (W_LLVMFuzzerTestOneInput_addI.zz_HOWN TfibB TfibB_syms)
    (W_LLVMFuzzerTestOneInput_addI.zz_HKEPT TfibB TfibB_syms)).
Qed.
Lemma topx_rig_HROMO : rom_out segs TfibB (G_RIG TfibB fr_RG).
Proof.
  apply (W_drain_pb.rom_out_incl _ _ _ _ (c_HG_RIG TfibB)).
  exact (c_rom_out TfibB TfibB_syms HEV).
Qed.

(* ---- the register images (relay_remove's HH59 / HH60 / HV4, relay_instance_gone's HH44 / HH45) ---- *)
Lemma topx_HH59 : VAL (A_HI 59) = rg_nsrc fr_RG + W_relay_remove_cx.RR_HI_NSRC.
Proof. vm_compute. reflexivity. Qed.
Lemma topx_HH60 : VAL (A_HI 60) = rg_src fr_RG + W_relay_remove_cx.RR_HI_SRC.
Proof. vm_compute. reflexivity. Qed.
Lemma topx_HV4 : VAL (A_OBJ 4) = rg_wake fr_RG + 4.
Proof. vm_compute. reflexivity. Qed.
Lemma topx_HH44 : VAL (A_HI 44) = rg_nsrc fr_RG + W_relay_instance_gone_cx.RIG_HI_NSRC.
Proof. vm_compute. reflexivity. Qed.
Lemma topx_HH45 : VAL (A_HI 45) = rg_src fr_RG + W_relay_instance_gone_cx.RIG_HI_SRC.
Proof. vm_compute. reflexivity. Qed.

(* ---- HRGP / HRGI (both walks, one text each) ---- *)
Lemma topx_HRGP : zpairwise_disjoint
[(rg_lock fr_RG, rg_lock fr_RG + 12); (rg_s fr_RG, rg_s fr_RG + 4 * ASRC); (rg_src fr_RG, rg_src fr_RG + 8);
 (rg_nsrc fr_RG, rg_nsrc fr_RG + 4); (rg_capsrc fr_RG, rg_capsrc fr_RG + 4);
 (rg_send_max fr_RG, rg_send_max fr_RG + 8); (rg_nout fr_RG, rg_nout fr_RG + 8);
 (rg_capout fr_RG, rg_capout fr_RG + 8); (rg_out fr_RG, rg_out fr_RG + 8); (rg_client fr_RG, rg_client fr_RG + 4);
 (rg_client_broken fr_RG, rg_client_broken fr_RG + 1); (rg_send_dead fr_RG, rg_send_dead fr_RG + 1);
 (rg_send_eintr fr_RG, rg_send_eintr fr_RG + 1); (rg_wake fr_RG + 4, rg_wake fr_RG + 8);
 (as_errno TfibB, as_errno TfibB + 4)].
Proof. apply W_drain_pb.zpairwise_disjb_ok. vm_compute. reflexivity. Qed.
Lemma topx_HRGI : forall a,
  (rg_capsrc fr_RG <= a < rg_capsrc fr_RG + 4 \/ rg_send_max fr_RG <= a < rg_send_max fr_RG + 8 \/
   rg_client fr_RG <= a < rg_client fr_RG + 4 \/ rg_send_dead fr_RG <= a < rg_send_dead fr_RG + 1) ->
  in_img segs a /\ ~ Exists (in_zr a) (as_owned_static TfibB).
Proof.
  intros a Ha.
  assert (Hg : inG (G_fr_c TfibB) a).
  { destruct Ha as [Ha | [Ha | [Ha | Ha]]].
    - exact (obj_c TfibB a (rng_cover (rg_capsrc fr_RG) 4 G_fr_obj ltac:(vm_compute; reflexivity) a Ha)).
    - exact (c_HG_smax TfibB a Ha).
    - exact (c_HG_client TfibB a Ha).
    - exact (c_HG_sdead TfibB a Ha). }
  exact (conj (c_img TfibB HEV a Hg) (W_LLVMFuzzerTestOneInput_addI.zz_HOWN TfibB TfibB_syms a Hg)).
Qed.

(* ---- HEND5L (both walks): the bytes of " end\0" (.str.4, A_OBJ 31 = 0x20f00), read-only ---- *)
Lemma topx_HEND5L : forall k, (k < 5)%nat -> YG0d.in_rom segs (VAL A_lit_end5 + Z.of_nat k) /\
  seg_rom segs (Z_to_bv 64 (VAL A_lit_end5 + Z.of_nat k)) = nth_error END5 k.
Proof.
  intros k Hk.
  destruct (TopxDrainLit.dlit_romb_ok (VAL A_lit_end5) ([32; 101; 110; 100] ++ [0]) ltac:(vm_compute; reflexivity))
    as [Hb Hr].
  split.
  - apply Hr. change (Z.of_nat (length ([32; 101; 110; 100] ++ [0]))) with 5. lia.
  - transitivity (option_map (Z_to_bv 8) (nth_error ([32; 101; 110; 100] ++ [0]) k)).
    + exact (Hb k ltac:(cbn [length app]; lia)).
    + unfold END5. rewrite nth_error_map. reflexivity.
Qed.

(* ---- HCANR (relay_instance_gone): __stack_chk_guard's 8 bytes are image bytes ---- *)
Lemma topx_HCANR : forall a, W_sites.FR_GUARD <= a < W_sites.FR_GUARD + 8 -> seg_rom segs (Z_to_bv 64 a) <> None.
Proof. intros a Ha. exact (rom_someb_ok W_sites.FR_GUARD 8 ltac:(vm_compute; reflexivity) a Ha). Qed.

(* ---- HLIT20 / HLIT21 / HLIT31 (relay_instance_gone), W_relay_instance_gone_cx.v's glit_at_x ---- *)
Lemma topx_HLIT20_x :
  W_relay_instance_gone_cx.glit_at_x (PI := PB_fr) ARX 20 (W_relay_instance_gone_cx.RIG_FMT ++ [0]).
Proof.
  unfold W_relay_instance_gone_cx.glit_at_x.
  destruct (TopxDrainLit.dlit_romb_ok (VAL (A_OBJ 20)) (W_relay_instance_gone_cx.RIG_FMT ++ [0])
    ltac:(vm_compute; reflexivity)) as [Hb Hr].
  split; [exact Hb|]. split; [exact Hr|]. split.
  - apply (W_shadow_pin_x.tfib_shp_x TfibB TfibB_syms _ TopxDrainLit.topx_dlit_ARX_laws). vm_compute. reflexivity.
  - exact (rom_tail_ok (VAL (A_OBJ 20)) (Z.of_nat (length (W_relay_instance_gone_cx.RIG_FMT ++ [0])))
      ltac:(vm_compute; reflexivity)).
Qed.
Lemma topx_HLIT21_x : W_relay_instance_gone_cx.glit_at_x (PI := PB_fr) ARX 21 (RelayModel.K_GESTURE ++ [0]).
Proof.
  unfold W_relay_instance_gone_cx.glit_at_x.
  destruct (TopxDrainLit.dlit_romb_ok (VAL (A_OBJ 21)) (RelayModel.K_GESTURE ++ [0])
    ltac:(vm_compute; reflexivity)) as [Hb Hr].
  split; [exact Hb|]. split; [exact Hr|]. split.
  - change (Z.of_nat (length (RelayModel.K_GESTURE ++ [0]))) with 14.
    exact (W_shadow_pin_x.ashp_gesture_14_fr_x TfibB TfibB_syms ARX TopxDrainLit.topx_dlit_ARX_laws).
  - exact (rom_tail_ok (VAL (A_OBJ 21)) (Z.of_nat (length (RelayModel.K_GESTURE ++ [0])))
      ltac:(vm_compute; reflexivity)).
Qed.
Lemma topx_HLIT31_x : W_relay_instance_gone_cx.glit_at_x (PI := PB_fr) ARX 31 ([32; 101; 110; 100] ++ [0]).
Proof.
  unfold W_relay_instance_gone_cx.glit_at_x.
  destruct (TopxDrainLit.dlit_romb_ok (VAL (A_OBJ 31)) ([32; 101; 110; 100] ++ [0])
    ltac:(vm_compute; reflexivity)) as [Hb Hr].
  split; [exact Hb|]. split; [exact Hr|]. split.
  - change (Z.of_nat (length ([32; 101; 110; 100] ++ [0]))) with 5.
    exact (W_shadow_pin_x.ashp_end5_5_fr_x TfibB TfibB_syms ARX TopxDrainLit.topx_dlit_ARX_laws).
  - exact (rom_tail_ok (VAL (A_OBJ 31)) (Z.of_nat (length ([32; 101; 110; 100] ++ [0])))
      ltac:(vm_compute; reflexivity)).
Qed.
End topx_relay.
