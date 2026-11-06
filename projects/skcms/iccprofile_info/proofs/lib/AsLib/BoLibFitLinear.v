(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.skcms.iccprofile_info.images Require Import AsanUbsan.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import PropExec CatExec CatSim SeqExec StoreOk SymExec Hoare Frame PropExecFP.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import LibDefs LibFPSpec LibFrame.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.AsLib Require Import AsSymExec AsSymExecSound AsSymRun AsSymDrive AsSymCall AsFuzzContract AsLibShadow AsLibDefs BoBase BoLibDefs AsRtSpec AsLibFPSpec AsLibTagsLib AsLibFPLib AsLibFrame AsLibEnv BoLibSpec AsLibPlace.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.AsLib Require Import AsSymDriveLZ.
Import ListNotations.
Open Scope bv_scope.
Import ASX. Import ASXS.
(* [comment removed for export] *)
Ltac disj_rel H := match type of H with context [?v] => is_var v; match goal with |- context [v] => idtac end end.
Ltac rlia := first [ (repeat match goal with H : _ \/ _ |- _ => tryif disj_rel H then fail else clear H end); dlia | dlia ].


Ltac Zify.zify_post_hook ::= idtac.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.   (* [comment removed for export] *)
From Stdlib Require Import Zify.
(* [comment removed for export] *)
Local Ltac el_t1 := (intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_post_hook); xlia zchecker.
(* [comment removed for export] *)
Local Ltac el_dm_pose x k := let v := eval vm_compute in k in lazymatch v with Zpos _ =>   (* [comment removed for export] *)
  lazymatch goal with _ : (x = k * (x / k) + x mod k)%Z |- _ => fail | _ =>
    pose proof (Z.div_mod x k ltac:(vm_compute; discriminate)); pose proof (Z.mod_pos_bound x k ltac:(vm_compute; reflexivity)) end end.
Local Ltac el_dm := repeat match goal with
  | |- context [ (?x / ?k)%Z ] => el_dm_pose x k
  | |- context [ (?x mod ?k)%Z ] => el_dm_pose x k
  | H : ?T |- _ => lazymatch T with (_ <= _)%Z => idtac | (_ < _)%Z => idtac | @eq Z _ _ => idtac | _ /\ _ => idtac | _ \/ _ => idtac end;
      match T with context [ (?x / ?k)%Z ] => el_dm_pose x k | context [ (?x mod ?k)%Z ] => el_dm_pose x k end
  end.
Local Ltac el_lia_core3 := first [ el_t1 | Zify.zify; xlia zchecker ].   (* [comment removed for export] *)
Local Ltac el_lia_core := first [ (intros; Zify.zify_pre_hook; zify_op; zify_iter_specs; Zify.zify_post_hook); xlia zchecker   (* [comment removed for export] *)
                                | el_t1 | ((progress el_dm); el_t1) ].
Local Ltac el_goal_has_var := match goal with |- ?G => match G with context [?x] => is_var x end end.
Local Ltac Lia.lia ::= tryif el_goal_has_var then el_lia_core else first [ solve [clear; el_lia_core] | el_lia_core ].
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac ev_simpl E ::=
  lazymatch goal with |- ?G =>
    let G1 := match tt with | _ => eval unfold E in G | _ => G end in
    let G2 := eval lazy [ev eb vals_ev blobs_ev nth app junk_vals fjunk_vals] in G1 in
    change G2
  end.
Local Ltac ev_simpl_in E H ::= try unfold E in H; lazy [ev eb vals_ev blobs_ev nth app junk_vals fjunk_vals] in H.
(* [comment removed for export] *)
#[local] Ltac AsSymDrive.run_fp_with_h HR HF HK fuel stops scr chints keep extra ::= run_fp_with_h_lz HR HF HK fuel stops scr chints keep extra.
#[local] Ltac AsSymDrive.branch_case_with HR HF HK Hc ::= branch_case_with_lz HR HF HK Hc.

(* [comment removed for export] *)
Ltac Zify.zify_post_hook ::= Z.div_mod_to_equations.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma mod32_16 : forall u k, (u mod 32 = 0)%Z -> (k mod 16 = 0)%Z -> ((u + k) mod 16 = 0)%Z.
Proof. intros u k Hu Hk. rlia. Qed.
Ltac Zify.zify_post_hook ::= idtac.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation SEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation TP := 0x5da970%Z.

(* [comment removed for export] *)
Ltac in_lit := cbn; repeat (first [left; reflexivity | right]).

(* [comment removed for export] *)
Lemma addwm1_lit : forall i, (1 <= i)%Z -> (i < 2 ^ 31)%Z ->
  sext 64 (alu32 ALU_ADD (low32 (Z_to_bv 64 i)) (low32 (Z_to_bv 64 (-1)))) = Z_to_bv 64 (i - 1).
Proof.
  intros i H1 H2. apply bv_eq. rewrite sext32_unsigned, Z_to_bv_unsigned.
  change (alu32 ALU_ADD (low32 (Z_to_bv 64 i)) (low32 (Z_to_bv 64 (-1)))) with (low32 (Z_to_bv 64 i) + low32 (Z_to_bv 64 (-1)))%bv.
  rewrite bv_add_unsigned, !low32_unsigned, !Z_to_bv_unsigned.
  unfold bv_swrap. rewrite !bv_wrap32_mod, !bv_wrap64_mod.
  change (bv_half_modulus 32) with (2 ^ 31)%Z.
  rewrite (Z.mod_small i (2 ^ 64)) by rlia. rewrite (Z.mod_small i (2 ^ 32)) by rlia.
  change (((-1) mod 2 ^ 64) mod 2 ^ 32)%Z with (2 ^ 32 - 1)%Z.
  replace (i + (2 ^ 32 - 1))%Z with ((i - 1) + 1 * 2 ^ 32)%Z by rlia. rewrite Z_mod_plus_full.
  rewrite (Z.mod_small (i - 1) (2 ^ 32)) by rlia.
  replace (i - 1 + 2 ^ 31)%Z with (i - 1 + 2 ^ 31)%Z by rlia. rewrite (Z.mod_small (i - 1 + 2 ^ 31) (2 ^ 32)) by rlia.
  replace (i - 1 + 2 ^ 31 - 2 ^ 31)%Z with (i - 1)%Z by rlia. rewrite ?Z.mod_small by rlia; reflexivity.
Qed.

Section Proof.
  Variable ceil : Z.
  Hypothesis Hev : eval_curve_contract_as SEGS as_both ceil.
  Hypothesis Hsm : stkmalloc0_contract SEGS as_both ceil.

  Variables (FPI : FPState) (regs : bvmap 5 word) (mem rom : word -> option byte).
  Variables (ret sp C data t8 t16 hc : word) (n len fs : Z) (bs : list byte) (ch : chain).

  Let S : Z := bv_unsigned sp.
  Let Fc : Z := frame0 fs (pos0 hc).                    (* [comment removed for export] *)
  Let h1 : word := Z_to_bv 64 (bv_unsigned hc + 1).     (* [comment removed for export] *)
  Let Ff : Z := frame0 fs (pos0 h1).                    (* [comment removed for export] *)
  Let faf : Z := (fs + FS_FLAGS0 + pos0 h1)%Z.           (* [comment removed for export] *)

  Hypothesis Hra : getr regs 1 = ret.
  Hypothesis Hret : ret_ok ret.
  Hypothesis Hsp : getr regs 2 = sp.
  Hypothesis Hc : getr regs 10 = C.
  Hypothesis H11 : getr regs 11 = Z_to_bv 64 n.
  Hypothesis H12 : getr regs 12 = Z_to_bv 64 (S + 20).
  Hypothesis H13 : getr regs 13 = Z_to_bv 64 (S + 16).
  Hypothesis H14 : getr regs 14 = Z_to_bv 64 (Fc + 32).
  Hypothesis Htp : getr regs 4 = Z_to_bv 64 TP.
  Hypothesis Hal32 : (S mod 32 = 0)%Z.
  Hypothesis Hstk : stackish ceil (S - FITLIN_D) (FITLIN_D + 24).
  Hypothesis Hwst : writable SEGS mem (S - FITLIN_D) (FITLIN_D + 24).
  Hypothesis Hshc : shz mem (S + 16) 1.
  Hypothesis Hcw : exists w, cell SEGS mem (S + 20) 4 w.
  Hypothesis Hwf : writable SEGS mem (Fc + 32) 4.
  Hypothesis Hsf : acell SEGS mem (AS_SB + (Fc + 32) / 8) 1 4.
  Hypothesis Hcal : (bv_unsigned C mod 8 = 0)%Z.
  Hypothesis Hch : heapish ceil (bv_unsigned C) 32.
  Hypothesis HshC : shz mem (bv_unsigned C) 3.
  Hypothesis Hcar : (fs + FS_FRAMES5 <= bv_unsigned C)%Z /\ (bv_unsigned C + 32 <= fs + FS_SIZE)%Z.
  Hypothesis Hn32 : (0 <= n < 2 ^ 32)%Z.
  Hypothesis Hn   : rdn SEGS mem (Z_to_bv 64 (bv_unsigned C + 0)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 n)).
  Hypothesis Ht8  : rdn SEGS mem (Z_to_bv 64 (bv_unsigned C + 8)) 8 = Some (word_to_le_bytes 8 t8).
  Hypothesis Ht16 : rdn SEGS mem (Z_to_bv 64 (bv_unsigned C + 16)) 8 = Some (word_to_le_bytes 8 t16).
  Hypothesis Hnr : (2 <= n <= 2 ^ 24)%Z.
  (* [comment removed for export] *)
  Hypothesis H8 : hidden (bv_unsigned t8 <> 0%Z -> inDATA data len (bv_unsigned t8) n).
  Hypothesis H16 : hidden (bv_unsigned t16 <> 0%Z -> inDATA data len (bv_unsigned t16) (2 * n)).
  Hypothesis Hsome : hidden (bv_unsigned t8 <> 0%Z \/ bv_unsigned t16 <> 0%Z).
  Hypothesis Hdok : as_data_ok ceil mem data len bs.
  Hypothesis Hdar : hidden (bv_unsigned data + len <= fs \/ fs + FS_SIZE <= bv_unsigned data)%Z.
  Hypothesis Henv : as_env SEGS ceil both_abi fs ch mem.
  Hypothesis Hhdr : fs_hdr SEGS ceil both_abi fs mem.
  Hypothesis Hfsw : fs_writable SEGS fs mem.
  Hypothesis Hhint : acellw SEGS mem (fs + FS_HINT0) h1.
  Hypothesis Hflags : fs_flags0_but fs [pos0 hc] mem.

  #[local] Abbreviation fp0 := (fp_regs (FPState:=FPI)).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma placement :
    (fs + FS_FRAMES0 <= Fc)%Z /\ (Fc + 64 <= fs + FS_FRAMES0 + FS_FRAMES_LEN)%Z /\ (Fc mod 64 = 0)%Z /\
    (fs + FS_FRAMES0 <= Ff)%Z /\ (Ff + 64 <= fs + FS_FRAMES0 + FS_FRAMES_LEN)%Z /\ (Ff mod 64 = 0)%Z /\
    (fs + FS_FLAGS0 <= faf)%Z /\ (faf < fs + FS_FLAGS0 + FS_FLAGS0_LEN)%Z /\
    (Fc + 64 <= Ff \/ Ff + 64 <= Fc)%Z /\ (faf <> fs + FS_FLAGS0 + pos0 hc)%Z /\
    (0 <= pos0 h1 < 16384)%Z /\ (0 <= pos0 hc < 16384)%Z.
  Proof using ceil mem sp C hc fs Hstk Hhdr.
    destruct Hhdr as (_ & _ & _ & Hlo & Hhi & Hal). pose proof (u64_range hc). pose proof (u64_range h1). app_facts.
    pose proof (pos_succ_ne hc) as Hne. fold h1 in Hne.
    pose proof (frame0_al64 fs (pos0 hc) Hal) as A1. pose proof (frame0_al64 fs (pos0 h1) Hal) as A2.
    unfold Fc, Ff, faf, frame0, FS_FRAMES0, FS_FRAMES_LEN, FS_FLAGS0, FS_FLAGS0_LEN.
    assert (B1 : (0 <= pos0 hc < 16384)%Z) by (unfold pos0; apply Z.mod_pos_bound; rlia).
    assert (B2 : (0 <= pos0 h1 < 16384)%Z) by (unfold pos0; apply Z.mod_pos_bound; rlia).
    revert Hne B1 B2 A1 A2. generalize (pos0 hc) (pos0 h1). intros p q Hne B1 B2 A1 A2.
    repeat split; first [assumption | rlia].
  Qed.

  Lemma quotients :
    Fc = (8 * (Fc / 8))%Z /\ Ff = (8 * (Ff / 8))%Z /\ bv_unsigned C = (8 * (bv_unsigned C / 8))%Z /\
    (fs + FS_FRAMES0 = 8 * ((fs + FS_FRAMES0) / 8))%Z /\ S = (8 * (S / 8))%Z /\
    bv_unsigned data = (8 * (bv_unsigned data / 8))%Z /\ (8 * (len / 8) <= len < 8 * (len / 8) + 8)%Z /\ True.
  Proof using ceil mem sp C data hc len fs bs Hal32 Hstk Hcal Hdok Hhdr.
    pose proof placement as (_ & _ & F3 & _ & _ & G3 & _).
    destruct Hhdr as (_ & _ & _ & _ & _ & Hal). destruct Hdok as (_ & _ & Hdal & _). unfold FS_FRAMES0. app_facts.
    split; [apply mod_exact; [rlia|]; apply (mod_down Fc 8 8); [rlia|rlia|exact F3]|].
    split; [apply mod_exact; [rlia|]; apply (mod_down Ff 8 8); [rlia|rlia|exact G3]|].
    split; [apply mod_exact; [rlia|exact Hcal]|].
    split. { apply mod_exact; [rlia|]. apply (mod_down _ 8 512); [rlia|rlia|]. change (8*512)%Z with 4096%Z.
             rewrite <- Zplus_mod_idemp_l, Hal. reflexivity. }
    split; [apply mod_exact; [rlia|]; apply (mod_down S 8 4); [rlia|rlia|exact Hal32]|].
    split; [apply mod_exact; [rlia|]; apply (mod_down _ 8 2); [rlia|rlia|exact Hdal]|].
    split; [apply div8_bounds| exact I].
  Qed.

  Ltac qlia := lazymatch goal with HQ : hidden (_ = _ /\ _) |- _ =>
    let Q1 := fresh "Q" in let Q2 := fresh "Q" in let Q3 := fresh "Q" in let Q4 := fresh "Q" in
    let Q5 := fresh "Q" in let Q6 := fresh "Q" in let Q7 := fresh "Q" in let Q8 := fresh "Q" in
    pose proof (unhide HQ) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8);
    first [ clear Q2 Q4 Q5 Q6 Q7 Q8; dlia | clear Q1 Q3 Q4 Q5 Q6 Q7 Q8; dlia | clear Q3 Q4 Q5 Q6 Q7 Q8; dlia
          | clear Q2 Q3 Q5 Q6 Q7 Q8; dlia | clear Q2 Q3 Q4 Q6 Q7 Q8; dlia | dlia ] end.
  Ltac opaque_lets := clearbody Fc Ff faf.

  (* [comment removed for export] *)
  Lemma EFf0 : (fs + 36864 + 0 * 2 ^ 20 + 64 * (bv_unsigned h1 mod 16384))%Z = Ff.
  Proof using sp C hc fs. unfold Ff, frame0, pos0, FS_FRAMES0. rlia. Qed.
  Lemma Efaf0 : (fs + 4096 + 0 + bv_unsigned h1 mod 16384)%Z = faf.
  Proof using sp C hc fs. unfold faf, pos0, FS_FLAGS0. rlia. Qed.
  Lemma Efaf' : (fs + FS_FLAGS0 + pos0 h1)%Z = faf. Proof using hc fs. reflexivity. Qed.
  Lemma EFc : frame0 fs (pos0 hc) = Fc. Proof using hc fs. reflexivity. Qed.
  Lemma div8_Fc32 : ((Fc + 32) / 8 = Fc / 8 + 4)%Z.
  Proof using sp C hc fs. replace (Fc + 32)%Z with (Fc + 8 * 4)%Z by rlia. apply div8_addk. Qed.
  Lemma div8_S16 : ((S + 16) / 8 = S / 8 + 2)%Z.
  Proof using sp C hc fs. replace (S + 16)%Z with (S + 8 * 2)%Z by rlia. apply div8_addk. Qed.
  Lemma SM16 : (S mod 16 = 0)%Z.
  Proof using sp Hal32. apply (mod_down S 16 2); [rlia|rlia|exact Hal32]. Qed.
  Lemma WFf : writable SEGS mem Ff 64.
  Proof using ceil mem sp C hc fs Hstk Hhdr Hfsw.
    pose proof placement as (_ & _ & _ & G1 & G2 & _). destruct Hhdr as (_ & _ & _ & Hlo & Hhi & _). destruct Hfsw as (_ & _ & _ & _ & Wfr0 & _). app_facts.
    unfold FS_FRAMES0, FS_FRAMES_LEN, FS_SIZE in *.
    eapply (writable_sub SEGS mem (fs + 36864) 1048576); [split; [rlia|split; [rlia|split; [rlia|exact Wfr0]]]|rlia|rlia|rlia].
  Qed.
  Lemma WSFf : writable SEGS mem (2147450880 + Ff / 8) 8.
  Proof using ceil mem sp C data hc len fs bs Hal32 Hstk Hcal Hdok Hhdr Hfsw.
    pose proof placement as (_ & _ & _ & G1 & G2 & _). pose proof quotients as (_ & Q2 & _ & Q4 & _).
    destruct Hhdr as (_ & _ & _ & Hlo & Hhi & _). destruct Hfsw as (_ & _ & _ & _ & _ & _ & Wsh0 & _). app_facts.
    unfold FS_FRAMES0, FS_FRAMES_LEN, FS_SIZE, AS_SB, FS_SHFRAMES_LEN in *.
    eapply (writable_sub SEGS mem (2147450880 + (fs + 36864) / 8) 131072); [split; [rlia|split; [rlia|split; [rlia|exact Wsh0]]]|rlia|rlia|rlia].
  Qed.
  Lemma Wfaf : writable SEGS mem faf 1.
  Proof using ceil mem sp C hc fs Hstk Hhdr Hfsw.
    pose proof placement as (_ & _ & _ & _ & _ & _ & G4 & G5 & _). destruct Hhdr as (_ & _ & _ & Hlo & Hhi & _). destruct Hfsw as (_ & _ & Wfl0 & _). app_facts.
    unfold FS_FLAGS0, FS_FLAGS0_LEN, FS_SIZE in *.
    eapply (writable_sub SEGS mem (fs + 4096) 16384); [split; [rlia|split; [rlia|split; [rlia|exact Wfl0]]]|rlia|rlia|rlia].
  Qed.
  Lemma Whint : writable SEGS mem (fs + 0) 8.
  Proof using ceil mem sp C hc fs Hstk Hhdr Hfsw.
    destruct Hhdr as (_ & _ & _ & Hlo & Hhi & _). destruct Hfsw as (Wh0 & _). unfold FS_SIZE, FS_HINT0 in *. app_facts.
    split; [rlia|split; [rlia|split; [rlia|exact Wh0]]].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition FTGT : list (word * Z) :=
    [(Z_to_bv 64 (S - FITLIN_D), (FITLIN_D + 24)%Z); (Z_to_bv 64 (Fc + 32), 4%Z);
     (Z_to_bv 64 (fs + FS_HINT0), 8%Z); (Z_to_bv 64 (fs + FS_FLAGS0 + pos0 h1), 1%Z);
     (Z_to_bv 64 Ff, 64%Z); (Z_to_bv 64 (AS_SB + Ff / 8), 8%Z)].

  Definition QP (FPI' : FPState) (regs' : bvmap 5 word) (mem' : word -> option byte) : Prop :=
    regs_kept abi_kept regs regs' /\ fregs_kept abi_fkept fp0 (fp_regs (FPState:=FPI')) /\
    (frame_mod mem mem' FTGT /\
     (exists w, cell SEGS mem' (S + 20) 4 w) /\ (exists w, cell SEGS mem' (Fc + 32) 4 w) /\
     acellw SEGS mem' (fs + FS_HINT0) (Z_to_bv 64 (bv_unsigned hc + 2)) /\
     mem' (Z_to_bv 64 (fs + FS_FLAGS0 + pos0 h1)) = Some (Z_to_bv 8 0) /\
     exists r, getr regs' 10 = Z_to_bv 64 r /\ (1 <= r <= n)%Z).
  Definition Q (st' : machine_state) : Prop :=
    exists (FPI' : FPState) regs' mem', st' = mkst (FP:=FPI') regs' ret mem' rom /\ QP FPI' regs' mem'.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac rewrite_getr_in H :=
    repeat match goal with G : getr ?R ?r = _ |- _ => rewrite G in H end.
  Ltac ev_simpl_goal := match goal with HK : know_ok _ ?E0 _ _ |- _ => ev_simpl E0 end.
  Ltac regions_eq :=
    repeat (lazymatch goal with
            | |- (_ :: _) = (_ :: _) => apply f_equal2; [apply f_equal2; [apply (f_equal (Z_to_bv 64)); unfold SB; first [(div8_facts; rlia) | qlia] | reflexivity] |]
            | |- [] = [] => reflexivity end).
  Ltac norm_denots E0 := cbn [regions_denot map fst snd]; unfold adenot; cbn [a_base a_off edenot]; ev_simpl E0;
                         unfold v_addi; rewrite ?u_srl3; rewrite_getr; rewrite ?u_small by clia.
  Ltac flats E0 := repeat (apply Forall_cons || apply Forall_nil); cbn [fst snd]; unfold flat, estart, elenZ; cbn [a_base a_off];
                   rewrite ?edenot_srl3; cbn [edenot]; ev_simpl E0; rewrite_getr; rewrite ?u_small by clia; unfold SB; first [(div8_facts; rlia) | qlia].
  Ltac frame_of_log RS :=
    lazymatch goal with
    | |- frame_mod ?M0 (mem_denot ?E0 ?M0 ?log) ?regions =>
        replace regions with (regions_denot E0 RS) by (norm_denots E0; regions_eq);
        apply (frame_mod_mem_denot E0 M0 log RS);
          [ lazymatch goal with H : log_flat _ log |- _ => exact H end
          | flats E0
          | vm_compute; reflexivity ]
    end.
  Ltac kframe HK Hfr RS :=
    lazymatch type of HK with know_ok _ ?E1 ?M0 ?kn =>
    lazymatch type of Hfr with frame_mod _ ?M' ?rs =>
      let Hrd := fresh "Hrd" in let Hrs := fresh "Hrs" in let Hfl := fresh "Hfl" in let H := fresh "HK" in
      assert (Hrd : regions_denot E1 RS = rs) by (norm_denots E1; regions_eq);
      assert (Hrs : frame_mod M0 M' (regions_denot E1 RS)) by (rewrite Hrd; exact Hfr);
      assert (Hfl : Forall (fun r => flat E1 (fst r) (snd r)) RS) by (flats E1);
      pose proof (know_ok_frame_mod SEGS E1 RS M0 M' kn HK Hfl Hrs) as H;
      let kn' := eval vm_compute in (kn_frames kn RS) in
      change (kn_frames kn RS) with kn' in H;
      clear Hrd Hrs Hfl HK; rename H into HK
    end end.
  Ltac kcell HK b k n v H :=
    lazymatch type of HK with know_ok _ ?E0 ?M0 ?kn =>
      let KR := fresh "KR" in let Hfl := fresh "Hfl" in
      assert (KR : kread SEGS kn b k n = Some v) by (vm_compute; reflexivity);
      pose proof (kread_rdn SEGS E0 M0 kn b k n v HK KR ltac:(rlia) ltac:(rlia)) as H; clear KR;
      lazymatch type of H with ?FL -> _ =>
        assert (Hfl : FL) by (unfold flat, estart; cbn [a_base a_off]; rewrite ?edenot_srl3; cbn [edenot]; ev_simpl E0; rewrite_getr;
                              rewrite ?u_small by clia; unfold SB; first [(div8_facts; rlia) | qlia]);
        specialize (H Hfl); clear Hfl end;
      unfold adenot, v_addi in H; cbn [a_base a_off] in H; cbn [edenot] in H; ev_simpl_in E0 H; rewrite ?u_srl3 in H; rewrite_getr_in H;
      rewrite ?u_small in H by clia
    end.
  Ltac kcell_auto HK b k n H :=
    lazymatch type of HK with know_ok _ _ _ ?kn =>
      let r := eval vm_compute in (kread SEGS kn b k n) in
      lazymatch r with Some ?v => kcell HK b k n v H end end.
  Ltac kn_prefix HK entries :=
    lazymatch type of HK with know_ok _ ?E1 ?M1 ?kn1 =>
      let HK' := fresh "HK" in
      assert (HK' : know_ok SEGS E1 M1 (entries ++ kn1));
      [ apply know_ok_app; [| exact HK]; unfold know_ok; repeat (apply Forall_cons); try apply Forall_nil
      | clear HK; rename HK' into HK; cbn [app] in HK ]
    end.
  Ltac zone_split x :=
    let h := fresh "Fz" in
    first [ match goal with H : appm x ?n |- _ => pose proof (app_sh_lit x n H) as h end
          | match goal with H : appm x ?n /\ _ |- _ => pose proof (app_sh_lit x n (proj1 H)) as h end
          | match goal with H : (appm x ?n /\ _) /\ _ |- _ => pose proof (app_sh_lit x n (proj1 (proj1 H))) as h end
          | match goal with H : fs_hdr _ _ _ x _ |- _ => pose proof (app_sh_lit x _ (proj1 (proj2 (proj2 (proj2 H))))) as h end ];
    destruct h as [h|h].
  (* [comment removed for export] *)
  Ltac solve_apart_q :=
    unfold apart, SB; repeat (apply Forall_cons; [cbn [fst snd]; div8_facts; rewrite ?u_small_frame by first [clia | qlia];
       lazymatch goal with
       | |- context [ (2147450880 + _)%Z ] => first [(zone_split fs; clia) | (zone_split (bv_unsigned data); clia) | clia | dlia | qlia]
       | _ => first [clia | dlia | qlia] end |]);
    apply Forall_nil.

  Ltac kdisjA E0 := cbn [kentry_ok]; unfold estart; cbn [a_base a_off]; rewrite ?edenot_srl3; cbn [edenot]; ev_simpl E0;
                rewrite ?Hc, ?Hsp, ?u_small by clia; unfold SB; first [(div8_facts; rlia) | qlia].

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma FTGT_safe : Forall (env_safe ceil fs) FTGT /\ apart (fs + FS_SSL) 9 FTGT /\
    apart (bv_unsigned data) len FTGT /\ apart (SB + bv_unsigned data / 8) (len / 8 + 1) FTGT /\ apart (SB + bv_unsigned C / 8) 3 FTGT /\
    apart (bv_unsigned C) 24 FTGT /\ apart 0x9f920 8 FTGT /\ apart 0xa79b8 8 FTGT /\ apart (SB + (S / 8 + 2)) 1 FTGT.
  Proof using ceil mem sp C data hc len fs bs Hal32 Hstk Hcal Hch Hcar Hdok Hdar Hhdr.
    clear H8 H16 Hsome Hflags Hev Hsm Hcw.
    pose proof (u64_range C). pose proof (u64_range sp). pose proof (u64_range data).
    pose proof placement as (F1 & F2 & F3 & G1 & G2 & G3 & G4 & G5 & FF & AA & B1 & B2). pose proof quotients as HQ. hide HQ.
    destruct Hhdr as (_ & _ & _ & Hlo & Hhi & Hal). destruct Hstk as [St1 St2]. destruct Hch as [C1 C2]. destruct Hcar as [A1 A2]. app_facts.
    assert (Fimg : (0x5fc000 <= fs)%Z) by (destruct (app_img_lit _ _ Hlo); [unfold FS_SIZE in *; rlia | rlia]).
    pose proof (app_sh_lit _ _ Hlo) as Fsh.
    destruct Hdok as (_ & [D1 D2] & _ & _). pose proof (unhide Hdar) as Hdar1. pose proof (app_sh_lit _ _ D1) as Dsh.
    unfold FTGT, FITLIN_D, AS_SB, FS_SIZE, FS_FRAMES0, FS_FRAMES_LEN, FS_FLAGS0, FS_FLAGS0_LEN, FS_FRAMES5, FS_HINT0, FS_SSL,
           env_safe in *.
    replace (fs + 4096 + pos0 h1)%Z with faf by reflexivity. clear FF AA. opaque_lets.
    (* [comment removed for export] *)
    split; [ repeat (apply Forall_cons); try apply Forall_nil; cbn [fst snd]; unfold FS_SIZE, AS_SB;
             div8_facts; pose proof (div8_bounds fs); pose proof (div8_bounds (fs + 11571200));
             rewrite ?u_small by first [clia | qlia];
             [ (split; [clia | left; clia]) | (split; [clia | right; left; split; clia]) | (split; [clia | right; left; split; clia])
             | (split; [clia | right; left; split; clia]) | (split; [clia | right; left; split; clia])
             | (split; [clia | right; right; split; clia]) ] | ].
    split; [solve_apart_q|]. split; [solve_apart_q|]. split; [solve_apart_q|]. split; [solve_apart_q|].
    split; [solve_apart_q|]. split; [solve_apart_q|]. split; [solve_apart_q|]. solve_apart_q.
  Qed.

  Lemma env_at : forall M, frame_mod mem M FTGT ->
    as_data_ok ceil M data len bs /\ env_ro both_abi M /\ as_sb SEGS as_both M /\ shz M (bv_unsigned C) 3 /\
    as_env SEGS ceil both_abi fs ch M /\ fs_hdr SEGS ceil both_abi fs M /\ fs_writable SEGS fs M.
  Proof using ceil mem sp C data hc len fs bs ch Hal32 Hstk Hcal Hch HshC Hcar Hdok Hdar Henv Hhdr Hfsw.
    intros M HF. pose proof FTGT_safe as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9).
    pose proof (u64_range C). pose proof (u64_range data). destruct Hch as [C1 C2]. app_facts.
    destruct Hdok as (Hd0 & Hdh & Hdal & Hshd). pose proof Hd0 as (Hlen & _ & _ & Hdhi & _). destruct Hdh as [D1 D2]. 
    assert (HE : as_env SEGS ceil both_abi fs ch M) by (eapply as_env_frame; [exact both_abi_low | ceil_lo | fs_app | exact HF | exact T1 | exact Henv]).
    split. { split; [eapply data_ok_frame; [exact HF | exact Hd0 | exact T3]|]. split; [split; assumption|]. split; [exact Hdal|].
             eapply shdata_frame; [exact HF | exact Hshd | rlia | rlia | rlia | exact T4]. }
    split; [exact (proj1 (proj2 (proj2 HE)))|].
    split. { apply (proj2 (as_sb_both SEGS M)). destruct HE as (HC & _). pose proof (both_cells64 SEGS M HC) as (E1 & E2 & _).
             unfold sbcell, cell64, LibDefs.cell. unfold acell in E1, E2. split; [exact E1 | exact E2]. }
    split; [eapply shz_frame; [exact HF | exact HshC | rlia | rlia | exact T5]|].
    split; [exact HE|].
    split; [eapply fs_hdr_frame; [exact both_abi_low | ceil_lo | exact HF | exact T1 | exact T2 | exact Hhdr]|].
    eapply fs_writable_frame; [exact HF | exact Hfsw].
  Qed.

  Definition in_ftgt (b : word) (m : Z) : Prop :=
    exists b' n', In (b', n') FTGT /\ (bv_unsigned b' <= bv_unsigned b)%Z /\ (bv_unsigned b + m <= bv_unsigned b' + n')%Z.
  Lemma fincl_of : forall rs, Forall (fun r => in_ftgt (fst r) (snd r)) rs -> regions_incl rs FTGT.
  Proof using sp hc fs. intros rs H b m Hin. rewrite Forall_forall in H. exact (H (b, m) Hin). Qed.
  Lemma frame_FTGT_app : forall M1 M2 l,
    frame_mod mem M1 FTGT -> frame_mod M1 M2 l -> regions_incl l FTGT -> frame_mod mem M2 FTGT.
  Proof using mem sp C hc fs.
    intros M1 M2 l HA HB Hl. eapply frame_mod_incl; [| exact (frame_mod_trans _ _ _ _ _ HA HB)].
    intros b m Hin. apply in_app_or in Hin as [Hin|Hin]; [exists b, m; split; [exact Hin| rlia] | exact (Hl b m Hin)].
  Qed.
  Lemma ftgt_facts :
    in_ftgt (Z_to_bv 64 (S - 224)) 224 /\ in_ftgt (Z_to_bv 64 (S - 432)) 208 /\ in_ftgt (Z_to_bv 64 (S - 240)) 16 /\
    in_ftgt (Z_to_bv 64 (S - 208)) 208 /\ in_ftgt (Z_to_bv 64 (S + 20)) 4 /\ in_ftgt (Z_to_bv 64 (S + 16)) 4 /\
    in_ftgt (Z_to_bv 64 (fs + 0)) 8 /\ in_ftgt (Z_to_bv 64 faf) 1 /\
    in_ftgt (Z_to_bv 64 Ff) 24 /\ in_ftgt (Z_to_bv 64 Ff) 64 /\ in_ftgt (Z_to_bv 64 Ff) 8 /\ in_ftgt (Z_to_bv 64 (Ff + 24)) 8 /\
    in_ftgt (Z_to_bv 64 (Ff + 32)) 4 /\ in_ftgt (Z_to_bv 64 (Ff + 56)) 8 /\
    in_ftgt (Z_to_bv 64 (2147450880 + Ff / 8)) 8 /\ in_ftgt (Z_to_bv 64 (Fc + 32)) 4.
  Proof using ceil mem rom ret sp C data hc n len fs bs Hal32 Hstk Hcal Hch Hcar Hn32 Hnr Hdok Hhdr.
    clear H8 H16 Hsome Hflags Hev Hsm Hcw Hdar.
    pose proof (u64_range C). pose proof (u64_range sp).
    pose proof placement as (F1 & F2 & F3 & G1 & G2 & G3 & G4 & G5 & FF & AA & B1 & B2). pose proof quotients as HQ. hide HQ.
    destruct Hhdr as (_ & _ & _ & Hlo & Hhi & Hal). destruct Hstk as [St1 St2]. destruct Hch as [C1 C2]. app_facts.
    unfold FITLIN_D, FS_SIZE, FS_FRAMES0, FS_FRAMES_LEN, FS_FLAGS0, FS_FLAGS0_LEN, FS_FRAMES5 in *.
    clear FF AA. unfold in_ftgt, FTGT, FITLIN_D, FS_HINT0, FS_FLAGS0, AS_SB. replace (fs + 4096 + pos0 h1)%Z with faf by reflexivity. opaque_lets.
    Ltac fin := split; [first [solve [cbn; repeat (first [left; reflexivity | right])] | (cbn; tauto)] | rewrite ?u_small by first [rlia | qlia]; first [rlia | qlia]].
    Ltac p1 := exists (Z_to_bv 64 (S - 432)), (432 + 24)%Z; fin.
    Ltac p2 := exists (Z_to_bv 64 (Fc + 32)), 4%Z; fin.
    Ltac p3 := exists (Z_to_bv 64 (fs + 0)), 8%Z; fin.
    Ltac p4 := exists (Z_to_bv 64 faf), 1%Z; fin.
    Ltac p5 := exists (Z_to_bv 64 Ff), 64%Z; fin.
    Ltac p6 := exists (Z_to_bv 64 (2147450880 + Ff / 8)), 8%Z; fin.
    split; [p1|]. split; [p1|]. split; [p1|]. split; [p1|]. split; [p1|]. split; [p1|].
    split; [p3|]. split; [p4|].
    split; [p5|]. split; [p5|]. split; [p5|]. split; [p5|]. split; [p5|]. split; [p5|].
    split; [p6|]. p2.
  Qed.
  Ltac solve_fincl :=
    lazymatch goal with |- regions_incl ?rs _ => change (regions_incl rs FTGT) end; apply fincl_of;
    pose proof ftgt_facts as (?T1 & ?T2 & ?T3 & ?T4 & ?T5 & ?T6 & ?T7 & ?T8 & ?T9 & ?T10 & ?T11 & ?T12 & ?T13 & ?T14 & ?T15 & ?T16);
    repeat (apply Forall_cons); try apply Forall_nil; cbn [fst snd]; first [assumption | match goal with |- ?g => idtac "FINCL-MISS" g end].

  (* [comment removed for export] *)
  Ltac call_ec RET HFT spv cv nv t8v t16v :=
    lazymatch goal with |- runs_to _ (@mkst ?I ?R' _ ?M' _) _ =>
    lazymatch goal with HR : regs_ok _ _ R', HK : know_ok _ _ M' _ |- _ =>
      let EA := fresh "EA" in let HCn := fresh "HCn" in let HC8 := fresh "HC8" in let HC16 := fresh "HC16" in
      pose proof (env_at M' HFT) as EA;
      let HR2eq := fresh "HR2eq" in
      assert (HR2eq : getr R' 2 = Z_to_bv 64 (S - 224)) by (regv_lin HR (2%bv:reg); rewrite Hsp; apply (f_equal (Z_to_bv 64)); fold S; rlia);
      kcell HK cv 0%Z 4%nat (EExt false 0 4 nv) HCn; rewrite ext_val_zx4_lit in HCn by rlia;
      kcell HK cv 8%Z 8%nat t8v HC8; kcell HK cv 16%Z 8%nat t16v HC16;
      eapply rt_call;
      [ eapply (Hev data len bs I R' M' rom (Z_to_bv 64 RET));
        [ regv HR (1%bv:reg); reflexivity
        | apply ret_ok_even; rewrite u_small by clia; reflexivity
        | unfold eval_curve_pre_as; cbn [al_abi as_both];
          exists C, t8, t16, n; split; [regv HR (10%bv:reg); rewrite_getr; reflexivity|];
          split; [exact Hcal|]; split; [exact Hch|];
          split; [unfold table_curve; split; [split; [exact Hn32| unfold LibDefs.cell; rewrite <- (Z.add_0_r (bv_unsigned C)); exact HCn]|];
                  split; [exact HC8|]; split; [exact HC16|]; split; [exact Hnr|];
                  split; [exact (unhide H8)|]; split; [exact (unhide H16)|]; exact (unhide Hsome) |];
          split; [exact (proj1 EA)|]; split; [exact (proj1 (proj2 EA))|];
          split; [exact (proj1 (proj2 (proj2 (proj2 EA))))|]; split; [exact (proj1 (proj2 (proj2 EA)))|];
          exists (Z_to_bv 64 (S - 224)); split; [regv_lin HR (2%bv:reg); rewrite Hsp; apply (f_equal (Z_to_bv 64)); fold S; rlia|];
          unfold as_frame, stackish; rewrite !u_small by clia;
          split; [rlia|]; split; [replace (S - 224)%Z with (S + (-224))%Z by rlia; apply mod32_16; [exact Hal32|reflexivity]|];
          eapply writable_frame; [exact HFT|]; eapply writable_sub; [exact Hwst|rlia|rlia|rlia] ]
      | cbv beta; clear EA HCn HC8 HC16;
        let FPI' := fresh "FPI" in let regs' := fresh "R" in let mem' := fresh "MC" in
        let Hkeep := fresh "Hkeep" in let Hfkeep := fresh "Hfkeep" in let Hmem := fresh "Hfr" in
        intros FPI' regs' mem' (Hkeep & Hfkeep & Hmem); unfold eval_curve_post_as in Hmem;
        rewrite HR2eq, (u_small (S - 224)) in Hmem by clia; replace (S - 224 - 16)%Z with (S - 240)%Z in Hmem by rlia; clear HR2eq;
        unfold regs_kept in Hkeep; unfold fregs_kept in Hfkeep;
        after_call Hkeep Hfkeep FPI'; clear Hkeep Hfkeep;
        lazymatch goal with HK' : know_ok _ _ M' _ |- _ => kframe HK' Hmem [(SA spv (-240), 16%Z)] end ]
    end end.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition lit8 (a v : Z) : kentry := KWord (SA (ELit 0) a) 8 (ELit v).

  (* [comment removed for export] *)
  Definition SAVED (M : word -> option byte) : Prop :=
    cell64 SEGS M (S - 8) ret /\ cell64 SEGS M (S - 16) (getr regs 8) /\ cell64 SEGS M (S - 24) (getr regs 9) /\
    cell64 SEGS M (S - 32) (getr regs 18) /\ cell64 SEGS M (S - 40) (getr regs 19) /\ cell64 SEGS M (S - 48) (getr regs 20) /\
    cell64 SEGS M (S - 56) (getr regs 21) /\ cell64 SEGS M (S - 64) (getr regs 22) /\ cell64 SEGS M (S - 72) (getr regs 23) /\
    cell64 SEGS M (S - 80) (getr regs 24) /\ cell64 SEGS M (S - 88) (getr regs 25) /\ cell64 SEGS M (S - 96) (getr regs 26) /\
    cell64 SEGS M (S - 104) (getr regs 27) /\
    cell64 SEGS M (S - 112) (reg_get fp0 8) /\ cell64 SEGS M (S - 120) (reg_get fp0 9) /\ cell64 SEGS M (S - 128) (reg_get fp0 18) /\
    cell64 SEGS M (S - 136) (reg_get fp0 19) /\ cell64 SEGS M (S - 144) (reg_get fp0 20).
  Definition SPILLS (M : word -> option byte) : Prop :=
    cell64 SEGS M (S - 152) (Z_to_bv 64 Ff) /\ cell64 SEGS M (S - 168) (Z_to_bv 64 (S + 16)) /\ cell64 SEGS M (S - 176) (Z_to_bv 64 Ff) /\
    cell64 SEGS M (S - 184) (Z_to_bv 64 Ff) /\ cell64 SEGS M (S - 192) (Z_to_bv 64 SB) /\ cell64 SEGS M (S - 200) (Z_to_bv 64 3) /\
    cell64 SEGS M (S - 208) (Z_to_bv 64 7).
  Definition MEMFIX (M : word -> option byte) : Prop :=
    SAVED M /\ SPILLS M /\
    acell SEGS M (SB + Fc / 8 + 4) 1 4 /\ shz M (S + 16) 1 /\
    cell SEGS M (bv_unsigned C) 4 (Z_to_bv 64 n) /\ cell64 SEGS M (bv_unsigned C + 8) t8 /\ cell64 SEGS M (bv_unsigned C + 16) t16 /\
    acell SEGS M (Ff + 56) 8 faf /\ acellw SEGS M (fs + 0) (Z_to_bv 64 (bv_unsigned hc + 2)) /\ frame_mod mem M FTGT.

  Definition REGFIX (FPI' : FPState) (R : bvmap 5 word) : Prop :=
    getr R 2 = Z_to_bv 64 (S - 224) /\ getr R 3 = getr regs 3 /\ getr R 4 = Z_to_bv 64 TP /\ getr R 8 = sp /\ getr R 9 = Z_to_bv 64 (S - 224) /\
    getr R 18 = Z_to_bv 64 0 /\
    getr R 20 = Z_to_bv 64 (Fc + 32) /\ getr R 21 = Z_to_bv 64 (S + 20) /\ getr R 22 = Z_to_bv 64 n /\ getr R 23 = C /\
    getr R 25 = alu64 ALU_ADD (alu64 ALU_SRL (Z_to_bv 64 Fc) (Z_to_bv 64 3)) (Z_to_bv 64 (SB + 4)) /\
    getr R 26 = alu64 ALU_ADD (alu64 ALU_SRL sp (Z_to_bv 64 3)) (Z_to_bv 64 (SB + 2)) /\
    getr R 27 = alu64 ALU_ADD (alu64 ALU_SRL (Z_to_bv 64 Ff) (Z_to_bv 64 3)) (Z_to_bv 64 SB) /\
    (forall r, In r [21; 22; 23; 24; 25; 26; 27]%bv -> reg_get (fp_regs (FPState:=FPI')) r = reg_get fp0 r).

  Definition TINV (lp : Z) (FPI' : FPState) (R : bvmap 5 word) (M : word -> option byte) : Prop :=
    REGFIX FPI' R /\ getr R 19 = Z_to_bv 64 lp /\ (1 <= lp <= n)%Z /\ MEMFIX M /\
    (exists wf, cell SEGS M (Fc + 32) 4 wf) /\ (exists wc, cell SEGS M (S + 20) 4 wc).
  Definition INV (i lp : Z) (FPI' : FPState) (R : bvmap 5 word) (M : word -> option byte) : Prop :=
    TINV lp FPI' R M /\ getr R 24 = Z_to_bv 64 i /\ (1 <= i <= n - 1)%Z.

  (* [comment removed for export] *)
  #[local] Abbreviation VALS R FR i lp wf wc :=
    (junk_vals R ++ fjunk_vals FR ++ junk_vals regs ++ fjunk_vals fp0 ++
     [Z_to_bv 64 n; t8; t16; Z_to_bv 64 Fc; Z_to_bv 64 fs; Z_to_bv 64 Ff; Z_to_bv 64 faf; Z_to_bv 64 i; Z_to_bv 64 lp; wf; wc]).

  Definition SRT : list expr :=
    [ELit 0; EVar 1; EAlu ALU_ADD (EVar 66) (ELit (-224)); EVar 67; ELit TP; EVar 5; EVar 6; EVar 7;
     EVar 66; EAlu ALU_ADD (EVar 66) (ELit (-224)); EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17;
     ELit 0; EVar 136; EAlu ALU_ADD (EVar 131) (ELit 32);
     EAlu ALU_ADD (EVar 66) (ELit 20); EVar 128; EVar 74; EVar 24; EAlu ALU_ADD (EAlu ALU_SRL (EVar 131) (ELit 3)) (ELit (SB + 4));
     EAlu ALU_ADD (EAlu ALU_SRL (EVar 66) (ELit 3)) (ELit (SB + 2)); EAlu ALU_ADD (EAlu ALU_SRL (EVar 133) (ELit 3)) (ELit SB); EVar 28; EVar 29; EVar 30; EVar 31].
  Definition SRI : list expr :=
    [ELit 0; EVar 1; EAlu ALU_ADD (EVar 66) (ELit (-224)); EVar 67; ELit TP; EVar 5; EVar 6; EVar 7;
     EVar 66; EAlu ALU_ADD (EVar 66) (ELit (-224)); EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17;
     ELit 0; EVar 136; EAlu ALU_ADD (EVar 131) (ELit 32);
     EAlu ALU_ADD (EVar 66) (ELit 20); EVar 128; EVar 74; EVar 135; EAlu ALU_ADD (EAlu ALU_SRL (EVar 131) (ELit 3)) (ELit (SB + 4));
     EAlu ALU_ADD (EAlu ALU_SRL (EVar 66) (ELit 3)) (ELit (SB + 2)); EAlu ALU_ADD (EAlu ALU_SRL (EVar 133) (ELit 3)) (ELit SB); EVar 28; EVar 29; EVar 30; EVar 31].
  Definition SFR : list expr :=
    [EVar 32; EVar 33; EVar 34; EVar 35; EVar 36; EVar 37; EVar 38; EVar 39; EVar 40; EVar 41;
     EVar 42; EVar 43; EVar 44; EVar 45; EVar 46; EVar 47; EVar 48; EVar 49; EVar 50; EVar 51; EVar 52;
     EVar 117; EVar 118; EVar 119; EVar 120; EVar 121; EVar 122; EVar 123; EVar 60; EVar 61; EVar 62; EVar 63].

  Definition KN : list kentry :=
    [lit8 0x9f920 0xa79b8; lit8 0xa79b8 SB;
     KAlign (EVar 66) 32; KRange (EVar 66) (AS_STKLO + 432) (2 ^ 47 - 24); KWr (SA (EVar 66) (-432)) 456;
     KRange (EVar 128) 2 (2 ^ 24); KRange (EVar 135) 1 (2 ^ 24); KRange (EVar 136) 1 (2 ^ 24);
     KWord (SA (EVar 66) (-8)) 8 (EVar 65); KWord (SA (EVar 66) (-16)) 8 (EVar 72); KWord (SA (EVar 66) (-24)) 8 (EVar 73);
     KWord (SA (EVar 66) (-32)) 8 (EVar 82); KWord (SA (EVar 66) (-40)) 8 (EVar 83); KWord (SA (EVar 66) (-48)) 8 (EVar 84);
     KWord (SA (EVar 66) (-56)) 8 (EVar 85); KWord (SA (EVar 66) (-64)) 8 (EVar 86); KWord (SA (EVar 66) (-72)) 8 (EVar 87);
     KWord (SA (EVar 66) (-80)) 8 (EVar 88); KWord (SA (EVar 66) (-88)) 8 (EVar 89); KWord (SA (EVar 66) (-96)) 8 (EVar 90);
     KWord (SA (EVar 66) (-104)) 8 (EVar 91);
     KWord (SA (EVar 66) (-112)) 8 (EVar 104); KWord (SA (EVar 66) (-120)) 8 (EVar 105); KWord (SA (EVar 66) (-128)) 8 (EVar 114);
     KWord (SA (EVar 66) (-136)) 8 (EVar 115); KWord (SA (EVar 66) (-144)) 8 (EVar 116);
     KWord (SA (EVar 66) (-152)) 8 (EVar 133); KWord (SA (EVar 66) (-168)) 8 (EAlu ALU_ADD (EVar 66) (ELit 16));
     KWord (SA (EVar 66) (-176)) 8 (EVar 133); KWord (SA (EVar 66) (-184)) 8 (EVar 133); KWord (SA (EVar 66) (-192)) 8 (ELit SB);
     KWord (SA (EVar 66) (-200)) 8 (ELit 3); KWord (SA (EVar 66) (-208)) 8 (ELit 7);
     KWord (SA (EVar 66) 20) 4 (EVar 138);
     KAlign (EVar 131) 64; KRange (EVar 131) 1 (2 ^ 47 - 64); KWr (SA (EVar 131) 32) 4; KWord (SA (EVar 131) 32) 4 (EVar 137);
     KWord (SA (EAlu ALU_SRL (EVar 131) (ELit 3)) (SB + 4)) 1 (ELit 4);
     KZero (SA (EAlu ALU_SRL (EVar 66) (ELit 3)) (SB + 2)) (ELit 1);
     KAlign (EVar 74) 8; KRange (EVar 74) 1 (2 ^ 47 - 32); KZero (SA (EAlu ALU_SRL (EVar 74) (ELit 3)) SB) (ELit 3);
     KWord (SA (EVar 74) 0) 4 (EVar 128); KWord (SA (EVar 74) 8) 8 (EVar 129); KWord (SA (EVar 74) 16) 8 (EVar 130);
     KAlign (EVar 133) 64; KRange (EVar 133) 1 (2 ^ 47 - 64); KWr (SA (EVar 133) 0) 64;
     KWr (SA (EAlu ALU_SRL (EVar 133) (ELit 3)) SB) 8; KWord (SA (EVar 133) 56) 8 (EVar 134);
     KRange (EVar 134) 1 (2 ^ 47 - 1); KWr (SA (EVar 134) 0) 1;
     KDisj (SA (EVar 131) 0) 64 (SA (EVar 74) 0) 32; KDisj (SA (EVar 133) 0) 64 (SA (EVar 74) 0) 32; KDisj (SA (EVar 134) 0) 1 (SA (EVar 74) 0) 32;
     KDisj (SA (EVar 133) 0) 64 (SA (EVar 131) 0) 64; KDisj (SA (EVar 134) 0) 1 (SA (EVar 131) 0) 64; KDisj (SA (EVar 133) 0) 64 (SA (EVar 134) 0) 1;
     KDisj (SA (EAlu ALU_SRL (EVar 133) (ELit 3)) SB) 8 (SA (EAlu ALU_SRL (EVar 74) (ELit 3)) SB) 3;
     KDisj (SA (EAlu ALU_SRL (EVar 133) (ELit 3)) SB) 8 (SA (EAlu ALU_SRL (EVar 131) (ELit 3)) (SB + 4)) 1;
     KDisj (SA (EAlu ALU_SRL (EVar 131) (ELit 3)) (SB + 4)) 1 (SA (EAlu ALU_SRL (EVar 74) (ELit 3)) SB) 3;
     (* [comment removed for export] *)
     KDisj (SA (EVar 131) 0) 64 ZSH ZSHL; KDisj (SA (EVar 131) 0) 64 ZIMG ZIMGL; KDisj (SA (EVar 131) 0) 64 (SA (EVar 66) (-432)) 464;
     KDisj (SA (EVar 74) 0) 32 ZSH ZSHL; KDisj (SA (EVar 74) 0) 32 ZIMG ZIMGL; KDisj (SA (EVar 74) 0) 32 (SA (EVar 66) (-432)) 464;
     KDisj (SA (EVar 133) 0) 64 ZSH ZSHL; KDisj (SA (EVar 133) 0) 64 ZIMG ZIMGL; KDisj (SA (EVar 133) 0) 64 (SA (EVar 66) (-432)) 464;
     KDisj (SA (EVar 134) 0) 1 ZSH ZSHL; KDisj (SA (EVar 134) 0) 1 ZIMG ZIMGL; KDisj (SA (EVar 134) 0) 1 (SA (EVar 66) (-432)) 464].

  Lemma pack : forall (lp i : Z) (FPI' : FPState) (R : bvmap 5 word) (M : word -> option byte) (wf wc : word),
    REGFIX FPI' R -> getr R 19 = Z_to_bv 64 lp -> (1 <= lp <= n)%Z -> (1 <= i <= n)%Z ->
    MEMFIX M -> cell SEGS M (Fc + 32) 4 wf -> cell SEGS M (S + 20) 4 wc ->
    let E := Env (vals_ev (VALS R (fp_regs (FPState:=FPI')) i lp wf wc)) (blobs_ev [bs]) in
    regs_ok E SRT R /\ fregs_ok E SFR (fp_regs (FPState:=FPI')) /\ know_ok SEGS E M KN /\
    regs_ok E (sr_vars 64) regs /\ fregs_ok E (sfr_vars 96) fp0.
  Proof using ceil FPI regs mem ret sp C data t8 t16 hc n len fs bs ch Hra Hsp Hc Hal32 Hstk Hwst Hwf Hcal Hch HshC Hcar Hn32 Hnr Hdok Hdar Henv Hhdr Hfsw.
    intros lp i FPI' R M wf wc (R2 & R3 & R4 & R8 & R9 & R18 & R20 & R21 & R22 & R23 & R25 & R26 & R27 & FK) R19 Hlp Hi
           ((V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8 & V9 & V10 & V11 & V12 & V13 & V14 & V15 & V16 & V17 & V18) &
            (P1 & P2 & P3 & P4 & P5 & P6 & P7) & Msf & Mshc & Mn & M8c & M16c & Mfp & Mh & MFT) Hwf' Hwc' E.
    clear H8 H16 Hsome Hflags Hev Hsm Hcw.
    pose proof (u64_range sp) as Hspr. pose proof (u64_range C) as HCr.
    pose proof placement as (F1 & F2 & F3 & G1 & G2 & G3 & G4 & G5 & FF & AA & B1 & B2). pose proof quotients as HQ. hide HQ.
    destruct Hhdr as (_ & _ & _ & Hlo & Hhi & Hal). destruct Hstk as [St1 St2]. destruct Hch as [C1 C2]. destruct Hcar as [A1 A2]. app_facts.
    pose proof (writable_frame SEGS mem M _ _ _ MFT Hwst) as (_ & _ & _ & Wst4).
    pose proof (writable_frame SEGS mem M _ _ _ MFT Hwf) as (_ & _ & _ & Wf4).
    pose proof (writable_frame SEGS mem M _ _ _ MFT WFf) as (_ & _ & _ & WFf4).
    pose proof (writable_frame SEGS mem M _ _ _ MFT WSFf) as (_ & _ & _ & WSFf4).
    pose proof (writable_frame SEGS mem M _ _ _ MFT Wfaf) as (_ & _ & _ & Wfaf4).
    destruct (env_at M MFT) as (_ & _ & _ & MshC & ME & _).
    destruct ME as (Hcells & _ & _ & _). pose proof (both_cells64 SEGS M Hcells) as (E1 & E2 & _). unfold acell in E1, E2.
    unfold FITLIN_D, AS_SB, FS_SIZE, FS_FRAMES0, FS_FRAMES_LEN, FS_FLAGS0, FS_FLAGS0_LEN, FS_FRAMES5 in *.
    clear AA MFT Mh. unfold cell64, cell, acell in *. opaque_lets.
    split; [|split; [|split; [|split]]].
    - replace SRT with (sr_upds (sr_vars 0)
        [(2, EAlu ALU_ADD (EVar 66) (ELit (-224))); (3, EVar 67); (4, ELit TP); (8, EVar 66); (9, EAlu ALU_ADD (EVar 66) (ELit (-224)));
         (18, ELit 0); (19, EVar 136); (20, EAlu ALU_ADD (EVar 131) (ELit 32));
         (21, EAlu ALU_ADD (EVar 66) (ELit 20)); (22, EVar 128); (23, EVar 74);
         (25, EAlu ALU_ADD (EAlu ALU_SRL (EVar 131) (ELit 3)) (ELit (SB + 4))); (26, EAlu ALU_ADD (EAlu ALU_SRL (EVar 66) (ELit 3)) (ELit (SB + 2)));
         (27, EAlu ALU_ADD (EAlu ALU_SRL (EVar 133) (ELit 3)) (ELit SB))]%bv) by (vm_compute; reflexivity).
      apply regs_ok_pins; [exact (regs_ok_vars [] R _ (blobs_ev [bs]))|].
      repeat (apply Forall_cons; [cbn [fst snd edenot]; ev_simpl E; rewrite_getr; rewrite ?alu_add_lit; rewrite ?Hsp; rewrite ?u_srl3; rewrite ?u_small by clia;
                                  first [ reflexivity | apply (f_equal (Z_to_bv 64)); rlia ] |]).
      apply Forall_nil.
    - replace SFR with (sr_upds (sfr_vars 32)
        [(21, EVar 117); (22, EVar 118); (23, EVar 119); (24, EVar 120); (25, EVar 121); (26, EVar 122); (27, EVar 123)]%bv)
        by (vm_compute; reflexivity).
      apply fregs_ok_pins; [exact (fregs_ok_vars (junk_vals R) (fp_regs (FPState:=FPI')) _ (blobs_ev [bs]))|].
      repeat (apply Forall_cons; [cbn [fst snd edenot]; ev_simpl E; apply FK; in_lit |]).
      apply Forall_nil.
    - unfold KN, lit8, know_ok.
      repeat lazymatch goal with |- Forall _ (_ :: _) => constructor | |- Forall _ [] => constructor end.
      all: lazymatch goal with |- Forall _ _ => fail | _ => idtac end.
      Ltac kw E0 H := eapply (kword_intro SEGS _ _ (EVar 66) sp _ _ _ _);
                      [cbn [edenot]; ev_simpl E0; exact Hsp | cbn [edenot]; ev_simpl E0; rewrite ?alu_add_lit, ?Hsp, ?u_small by clia; reflexivity | rlia | rlia | fold S; rlia | fold S; rlia |
                       fold S; lazymatch goal with |- rdn _ _ (Z_to_bv 64 ?a) _ = _ =>
                         lazymatch type of H with rdn _ _ (Z_to_bv 64 ?b) _ = _ => replace a with b by rlia; rewrite_getr; exact H end end].
      Ltac klitA E0 H := eapply (kword_intro SEGS E0 _ (ELit 0) (Z_to_bv 64 0));
        [reflexivity | cbn [edenot]; ev_simpl E0; reflexivity | rlia | rlia | rewrite u_lit0; rlia | rewrite u_lit0; rlia | rewrite u_lit0, Z.add_0_l; exact H].
      + klitA E E1. + klitA E E2.
      + apply kalign_intro; [rlia | cbn [edenot]; ev_simpl E; rewrite Hsp; exact Hal32].
      + apply krange_intro; cbn [edenot]; ev_simpl E; rewrite Hsp; fold S; rlia.
      + apply (kwr_intro SEGS E M (EVar 66) sp (-432) 456); [cbn [edenot]; ev_simpl E; exact Hsp | fold S; rlia | rlia | fold S; rlia |].
        fold S. replace (S + -432)%Z with (S - 432)%Z by rlia. exact Wst4.
      + apply krange_intro; cbn [edenot]; ev_simpl E; rewrite u_small by clia; rlia.
      + apply krange_intro; cbn [edenot]; ev_simpl E; rewrite u_small by clia; rlia.
      + apply krange_intro; cbn [edenot]; ev_simpl E; rewrite u_small by clia; rlia.
      + kw E V1. + kw E V2. + kw E V3. + kw E V4. + kw E V5. + kw E V6. + kw E V7. + kw E V8. + kw E V9. + kw E V10.
      + kw E V11. + kw E V12. + kw E V13. + kw E V14. + kw E V15. + kw E V16. + kw E V17. + kw E V18.
      + kw E P1. + kw E P2. + kw E P3. + kw E P4. + kw E P5. + kw E P6. + kw E P7.
      + kw E Hwc'.
      + apply kalign_intro; [rlia | cbn [edenot]; ev_simpl E; rewrite u_small by clia; exact F3].
      + apply krange_intro; cbn [edenot]; ev_simpl E; rewrite u_small by clia; rlia.
      + apply (kwr_intro SEGS E M (EVar 131) (Z_to_bv 64 Fc) 32 4); [cbn [edenot]; ev_simpl E; reflexivity | rewrite u_small by clia; rlia | rlia | rewrite u_small by clia; rlia |].
        rewrite u_small by clia. exact Wf4.
      + eapply (kword_intro SEGS E M (EVar 131) (Z_to_bv 64 Fc) 32 4 (EVar 137) wf);
          [cbn [edenot]; ev_simpl E; reflexivity | cbn [edenot]; ev_simpl E; reflexivity | rlia | rlia | rewrite u_small by clia; rlia | rewrite u_small by clia; rlia | rewrite u_small by clia; exact Hwf'].
      + eapply (kword_intro SEGS E M (EAlu ALU_SRL (EVar 131) (ELit 3)) _ (SB + 4) 1 (ELit 4) (Z_to_bv 64 4));
          [reflexivity | cbn [edenot]; ev_simpl E; reflexivity | rlia | rlia | rewrite edenot_srl3; cbn [edenot]; ev_simpl E; rewrite u_small by clia; unfold SB; qlia
          | rewrite edenot_srl3; cbn [edenot]; ev_simpl E; rewrite u_small by clia; unfold SB; qlia |].
        rewrite edenot_srl3. cbn [edenot]; ev_simpl E. rewrite u_small by clia. unfold SB in *.
        replace (Fc / 8 + (2147450880 + 4))%Z with (2147450880 + Fc / 8 + 4)%Z by rlia. exact Msf.
      + eapply (kzero_shadow_intro SEGS E M (EVar 66) sp 2 1); [cbn [edenot]; ev_simpl E; exact Hsp | rlia | rlia | fold S; qlia |].
        intros j Hj. fold S. destruct Mshc as [_ Hz]. rewrite div8_S16 in Hz. replace (SB + S / 8 + j)%Z with (SB + (S / 8 + 2) + (j - 2))%Z by rlia. apply Hz. rlia.
      + apply kalign_intro; [rlia | cbn [edenot]; ev_simpl E; rewrite Hc; exact Hcal].
      + apply krange_intro; cbn [edenot]; ev_simpl E; rewrite Hc; rlia.
      + eapply (kzero_shz_intro SEGS E M (EVar 74) C 3); [cbn [edenot]; ev_simpl E; exact Hc | exact MshC | rlia | rlia].
      + eapply (kword_intro SEGS E M (EVar 74) C 0 4 (EVar 128) (Z_to_bv 64 n)); cbn; rewrite ?Hc; try rlia; auto. rewrite Z.add_0_r. exact Mn.
      + eapply (kword_intro SEGS E M (EVar 74) C 8 8 (EVar 129) t8); cbn; rewrite ?Hc; try rlia; auto.
      + eapply (kword_intro SEGS E M (EVar 74) C 16 8 (EVar 130) t16); cbn; rewrite ?Hc; try rlia; auto.
      + apply kalign_intro; [rlia | cbn [edenot]; ev_simpl E; rewrite u_small by clia; exact G3].
      + apply krange_intro; cbn [edenot]; ev_simpl E; rewrite u_small by clia; rlia.
      + apply (kwr_intro SEGS E M (EVar 133) (Z_to_bv 64 Ff) 0 64); [cbn [edenot]; ev_simpl E; reflexivity | rewrite u_small by clia; rlia | rlia | rewrite u_small by clia; rlia |].
        rewrite u_small, Z.add_0_r by rlia. exact WFf4.
      + replace SB with (SB + 0)%Z by rlia. eapply (kwr_shadow_intro SEGS E M (EVar 133) (Z_to_bv 64 Ff) 0 8);
          [cbn [edenot]; ev_simpl E; reflexivity | rlia | rlia | rewrite u_small by clia; qlia | rewrite u_small, Z.add_0_r by rlia; unfold SB; exact WSFf4].
      + eapply (kword_intro SEGS E M (EVar 133) (Z_to_bv 64 Ff) 56 8 (EVar 134) (Z_to_bv 64 faf));
          [cbn [edenot]; ev_simpl E; reflexivity | cbn [edenot]; ev_simpl E; reflexivity | rlia | rlia
          | rewrite u_small by clia; rlia | rewrite u_small by clia; rlia | rewrite u_small by clia; exact Mfp].
      + apply krange_intro; cbn [edenot]; ev_simpl E; rewrite u_small by clia; rlia.
      + apply (kwr_intro SEGS E M (EVar 134) (Z_to_bv 64 faf) 0 1); [cbn [edenot]; ev_simpl E; reflexivity | rewrite u_small by clia; rlia | rlia | rewrite u_small by clia; rlia |].
        rewrite u_small, Z.add_0_r by rlia. exact Wfaf4.
      + kdisjA E. + kdisjA E. + kdisjA E. + kdisjA E. + kdisjA E. + kdisjA E. + kdisjA E. + kdisjA E. + kdisjA E.
      + kdisj_place. + kdisj_place. + kdisj_place. + kdisj_place. + kdisj_place. + kdisj_place.
      + kdisj_place. + kdisj_place. + kdisj_place. + kdisj_place. + kdisj_place. + kdisj_place.
    - exact (regs_ok_vars (junk_vals R ++ fjunk_vals (fp_regs (FPState:=FPI'))) regs
               (fjunk_vals fp0 ++ [Z_to_bv 64 n; t8; t16; Z_to_bv 64 Fc; Z_to_bv 64 fs; Z_to_bv 64 Ff; Z_to_bv 64 faf; Z_to_bv 64 i; Z_to_bv 64 lp; wf; wc]) (blobs_ev [bs])).
    - exact (fregs_ok_vars (junk_vals R ++ fjunk_vals (fp_regs (FPState:=FPI')) ++ junk_vals regs) fp0
               [Z_to_bv 64 n; t8; t16; Z_to_bv 64 Fc; Z_to_bv 64 fs; Z_to_bv 64 Ff; Z_to_bv 64 faf; Z_to_bv 64 i; Z_to_bv 64 lp; wf; wc] (blobs_ev [bs])).
  Qed.

  Lemma pack_I : forall (i lp : Z) (FPI' : FPState) (R : bvmap 5 word) (M : word -> option byte),
    INV i lp FPI' R M -> exists wf wc,
    let E := Env (vals_ev (VALS R (fp_regs (FPState:=FPI')) i lp wf wc)) (blobs_ev [bs]) in
    regs_ok E SRI R /\ fregs_ok E SFR (fp_regs (FPState:=FPI')) /\ know_ok SEGS E M KN /\
    regs_ok E (sr_vars 64) regs /\ fregs_ok E (sfr_vars 96) fp0.
  Proof using ceil FPI regs mem ret sp C data t8 t16 hc n len fs bs ch Hra Hsp Hc Hal32 Hstk Hwst Hwf Hcal Hch HshC Hcar Hn32 Hnr Hdok Hdar Henv Hhdr Hfsw.
    intros i lp FPI' R M ((HRF & R19 & Hlp & HMF & (wf & Hwf') & (wc & Hwc')) & R24 & Hi).
    exists wf, wc.
    destruct (pack lp i FPI' R M wf wc HRF R19 Hlp ltac:(rlia) HMF Hwf' Hwc') as (HR & HF & HK & H64 & H96).
    split; [|split; [exact HF| split; [exact HK | split; [exact H64 | exact H96]]]].
    apply (regs_ok_pin _ _ R 24 (EVar 135)) in HR; [| cbn [edenot ev eb vals_ev blobs_ev nth app junk_vals fjunk_vals]; exact R24].
    exact HR.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac subst_triv := repeat match goal with H : ?a = ?b |- _ => is_var a; is_var b; subst a end.
  Ltac solve_reg := rewrite_getr; rewrite ?alu_add_lit; rewrite ?addw1_lit by rlia; rewrite ?Hsp; rewrite ?u_small by clia;
                    rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; first [reflexivity | apply (f_equal (Z_to_bv 64)); fold S; rlia | idtac].
  Ltac creg r := lazymatch goal with HR : regs_ok _ _ ?R' |- getr ?R' _ = _ => regv HR r; solve_reg end.

  Ltac prove_regfix H64 H96 :=
    lazymatch goal with |- REGFIX ?I ?R' =>
    lazymatch goal with HR : regs_ok ?E ?sr R', HF : fregs_ok _ ?sfr (@fp_regs I) |- _ =>
      lift_id H64 HR; lift_id H96 HF; unfold REGFIX;
      split; [creg (2%bv:reg)|];
      split; [lazymatch type of H64 with id (regs_ok _ ?sr0 _) =>
                exact (regs_same_on E sr0 sr regs R' [3]%bv H64 HR ltac:(vm_compute; reflexivity) 3%bv ltac:(left; reflexivity)) end|];
      split; [regv HR (4%bv:reg); reflexivity|];
      split; [creg (8%bv:reg)|]; split; [creg (9%bv:reg)|]; split; [creg (18%bv:reg)|]; split; [creg (20%bv:reg)|];
      split; [creg (21%bv:reg)|]; split; [creg (22%bv:reg)|]; split; [creg (23%bv:reg)|]; split; [creg (25%bv:reg)|];
      split; [creg (26%bv:reg)|]; split; [creg (27%bv:reg)|];
      lazymatch type of H96 with id (fregs_ok _ ?sfr0 _) =>
          exact (fregs_same_on E sfr0 sfr fp0 _ [21; 22; 23; 24; 25; 26; 27]%bv H96 HF ltac:(vm_compute; reflexivity)) end
    end end.

  (* [comment removed for export] *)
  Lemma memfix_frame : forall M M' rs, MEMFIX M -> frame_mod M M' rs ->
    (rs = [(Z_to_bv 64 (S - 240), 16%Z)] \/ rs = [(Z_to_bv 64 (S + 20), 4%Z)]) -> MEMFIX M'.
  Proof using ceil FPI regs mem rom ret sp C data t8 t16 hc n len fs bs Hal32 Hstk Hcal Hch Hcar Hn32 Hnr Hdok Hhdr.
    intros M M' rs HM Hf Hrs.
    clear H8 H16 Hsome Hflags Hev Hsm Hcw.
    pose proof (u64_range sp). pose proof (u64_range C). pose proof placement as (F1 & F2 & F3 & G1 & G2 & G3 & G4 & G5 & FF & AA & B1 & B2).
    pose proof quotients as HQ. hide HQ.
    destruct Hhdr as (_ & _ & _ & Hlo & Hhi & Hal). destruct Hstk as [St1 St2]. destruct Hch as [C1 C2]. destruct Hcar as [A1 A2]. app_facts.
    unfold FITLIN_D, FS_SIZE, FS_FRAMES0, FS_FRAMES_LEN, FS_FLAGS0, FS_FLAGS0_LEN, FS_FRAMES5 in *.
    assert (HFT' : frame_mod mem M' FTGT).
    { destruct HM as (_ & _ & _ & _ & _ & _ & _ & _ & _ & MFT). eapply frame_FTGT_app; [exact MFT | exact Hf |].
      destruct Hrs as [-> | ->]; solve_fincl. }
    assert (AP : forall a m, (0 <= m)%Z -> (a + m <= S - 240 \/ S - 224 <= a)%Z -> (a + m <= S + 20 \/ S + 24 <= a)%Z -> apart a m rs).
    { intros a m Hm X Y. destruct Hrs as [-> | ->]; unfold apart; (apply Forall_cons; [cbn [fst snd]; rewrite u_small_frame by clia; rlia | apply Forall_nil]). }
    clear Hrs FF AA. opaque_lets.
    destruct HM as ((V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8 & V9 & V10 & V11 & V12 & V13 & V14 & V15 & V16 & V17 & V18) &
                    (P1 & P2 & P3 & P4 & P5 & P6 & P7) & Msf & Mshc & Mn & M8c & M16c & Mfp & Mh & MFT).
    unfold MEMFIX, SAVED, SPILLS.
    Ltac cf Hf AP := first
      [ eapply cell64_frame; [exact Hf | eassumption | rlia | rlia | apply AP; rlia]
      | eapply cell_frame; [exact Hf | eassumption | rlia | cbn; rlia | apply AP; cbn; rlia]
      | eapply acell_frame; [exact Hf | eassumption | first [rlia|qlia] | cbn; first [rlia|qlia] | apply AP; cbn; first [rlia|qlia]]
      | eapply acellw_frame; [exact Hf | eassumption | rlia | rlia | apply AP; rlia] ].
    repeat match goal with |- _ /\ _ => split end; try (cf Hf AP).
    - unfold SB. cf Hf AP.
    - eapply shz_frame; [exact Hf | exact Mshc | rlia | rlia | rewrite div8_S16; apply AP; unfold SB; first [rlia|qlia]].
    - exact HFT'.
  Qed.

  Ltac prove_memfix :=
    first
      [ assumption
      | lazymatch goal with |- MEMFIX ?Mx =>
          match goal with Hf : frame_mod ?M0 Mx ?rs, HM0 : MEMFIX ?M0 |- _ =>
            apply (memfix_frame M0 Mx rs HM0 Hf); first [left; reflexivity | right; reflexivity]
          end end ].

  Ltac prove_cell b k :=
    first
      [ assumption
      | lazymatch goal with |- exists _, cell _ ?Mx _ _ _ =>
          lazymatch goal with HK : know_ok _ _ Mx _ |- _ =>
            let H := fresh "HC" in kcell_auto HK b k 4%nat H; eexists; exact H end end ].

  Ltac prove_TINV H64 H96 :=
    unfold TINV;
    split; [prove_regfix H64 H96|];
    split; [creg (19%bv:reg)|];
    split; [rlia|];
    split; [prove_memfix|];
    split; [prove_cell (EVar 131) 32%Z | prove_cell (EVar 66) 20%Z].

  Ltac prove_INV H64 H96 :=
    unfold INV; split; [prove_TINV H64 H96 | split; [creg (24%bv:reg) | rlia]].

  Ltac norm_latch Hl :=
    lazymatch type of Hl with branch_taken _ (edenot ?E0 _) _ = _ =>
      rewrite branch_taken_Z in Hl; cbv beta iota in Hl; cbn [edenot] in Hl; ev_simpl_in E0 Hl;
      rewrite_getr_in Hl; rewrite ?alu_add_lit in Hl; rewrite ?addw1_lit in Hl by rlia; rewrite ?u_small in Hl by clia
    end.

  (* [comment removed for export] *)
  Ltac frame_store_c :=
    lazymatch goal with EQM : ?Mx = mem_denot ?E0 ?M0 ?log |- _ =>
      let Hf := fresh "HfC" in
      assert (Hf : frame_mod M0 Mx [(Z_to_bv 64 (S + 20), 4%Z)]) by (rewrite EQM; frame_of_log [(SA (EVar 66) 20, 4%Z)]);
      clear EQM end.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac post_regs :=
    lazymatch goal with
    | |- exists FPI' regs' mem', @mkst ?I ?R' _ ?M' _ = _ /\ _ =>
      lazymatch goal with
      | HR : regs_ok ?E1 ?sr R', HF : fregs_ok _ ?sfr (@fp_regs I), HR0 : id (regs_ok _ ?sr0 ?regs0), HF0 : id (fregs_ok _ ?sfr0 ?fr0) |- _ =>
        lift_id HR0 HR; lift_id HF0 HF;
        exists I, R', M'; split; [regv HR (1%bv:reg); rewrite_getr; reflexivity|];
        split; [ let Hso := fresh "Hso" in
                 pose proof (regs_same_on E1 sr0 sr regs0 R' [2;3;8;9;18;19;20;21;22;23;24;25;26;27]%bv HR0 HR ltac:(vm_compute; reflexivity)) as Hso;
                 intros r Hr; cbn [In abi_kept] in Hr;
                 destruct Hr as [<-|[<-|[<-|Hr]]]; [apply Hso; first [solve [cbn; repeat (first [left; reflexivity | right])] | (cbn; tauto)] | apply Hso; first [solve [cbn; repeat (first [left; reflexivity | right])] | (cbn; tauto)] | regv HR (4%bv:reg); rewrite Htp; reflexivity |];
                 apply Hso; cbn; cbn in Hr; tauto
               |];
        split; [exact (fregs_same_on E1 sfr0 sfr fr0 _ abi_fkept HF0 HF ltac:(vm_compute; reflexivity))|]
      end
    end.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma tail_ok : forall lp (FPI' : FPState) R M, TINV lp FPI' R M ->
    runs_to SEGS (mkst (FP:=FPI') R (Z_to_bv 64 0x87778) M rom) Q.
  Proof using ceil FPI regs mem rom ret sp C data t8 t16 hc n len fs bs ch Hra Hret Hsp Hc Htp Hal32 Hstk Hwst Hwf Hcal Hch HshC Hcar Hn32 Hnr Hdok Hdar Henv Hhdr Hfsw.
    intros lp FPI' R M HT.
    pose proof HT as (HRF & R19 & Hlp & HMF & (wf & Hwf') & (wc & Hwc')).
    pose proof (u64_range sp) as Hspr. pose proof (u64_range C) as HCr.
    pose proof placement as (F1 & F2 & F3 & G1 & G2 & G3 & G4 & G5 & FF & AA & B1 & B2). pose proof quotients as HQ. hide HQ. hide FF. clear AA.
    pose proof Hhdr as (_ & _ & _ & Hfslo & Hfshi & Hfsal). pose proof Hstk as [St1 St2]. pose proof Hch as [C1 C2]. pose proof Hcar as [A1 A2]. app_facts.
    unfold FITLIN_D, AS_SB, FS_SIZE, FS_FRAMES0, FS_FRAMES_LEN, FS_FLAGS0, FS_FLAGS0_LEN, FS_FRAMES5, FS_HINT0 in *.
    destruct (pack lp 1 FPI' R M wf wc HRF R19 Hlp ltac:(rlia) HMF Hwf' Hwc') as (HR & HF & HK & H64 & H96).
    pose proof (H64 : id _) as HR0. pose proof (H96 : id _) as HF0. clear H64 H96.
    pose proof HMF as (_ & _ & _ & _ & _ & _ & _ & Mfp & Mh & MFT).
    opaque_lets.
    (* [comment removed for export] *)
    run_fp 120%nat (@nil Z) noscr true; subst_triv. try clear HLF.
    branch_case as Ht.
    { exfalso. rewrite branch_taken_Z in Ht. cbv beta iota in Ht. cbn [edenot] in Ht.
      lazymatch type of HR with regs_ok ?E0 _ _ => ev_simpl_in E0 Ht end.
      rewrite_getr_in Ht. rewrite ?u_small in Ht by clia. rewrite addwm1_lit in Ht by rlia.
      rewrite !bv_signed_small in Ht by (rewrite u_small by clia; rlia). rewrite !u_small in Ht by clia.
      rewrite (proj2 (Z.ltb_lt _ _)) in Ht by rlia. discriminate Ht. }
    run_fp 120%nat (@nil Z) noscr true.
    assert (HFR9 : frame_mod M M0 [(Z_to_bv 64 (S + 16), 4%Z); (Z_to_bv 64 Ff, 8%Z); (Z_to_bv 64 (2147450880 + Ff / 8), 8%Z); (Z_to_bv 64 faf, 1%Z)]).
    { rewrite EQM. frame_of_log [(SA (EVar 66) 16, 4%Z); (SA (EVar 133) 0, 8%Z); (SA (EAlu ALU_SRL (EVar 133) (ELit 3)) SB, 8%Z); (SA (EVar 134) 0, 1%Z)]. }
    fin_ret. unfold Q, QP. post_regs.
    split; [|split; [|split; [|split; [|split]]]].
    - eapply frame_FTGT_app; [exact MFT | exact HFR9 | solve_fincl].
    - kcell_auto HK (EVar 66) 20%Z 4%nat HCc. eexists; exact HCc.
    - kcell_auto HK (EVar 131) 32%Z 4%nat HCf. eexists; exact HCf.
    - unfold FS_HINT0. eapply acellw_frame; [exact HFR9 | exact Mh | rlia | rlia | ]. pose proof (app_sh_lit _ _ Hfslo) as Fsh. solve_apart_q.
    - rewrite EQM.
      lazymatch type of HK with know_ok _ ?E2 _ _ =>
        replace (fs + FS_FLAGS0 + pos0 h1)%Z with (bv_unsigned (edenot E2 (EVar 134)) + 0)%Z
          by (cbn [edenot]; ev_simpl E2; rewrite u_small by clia; rewrite <- Efaf'; rlia);
        eapply (mem_denot_lzK_cover SEGS E2 _ _ _ _ (EVar 134) 0 1%nat HK HLF); [vm_compute; reflexivity | | | rlia];
        cbn [edenot]; ev_simpl E2; rewrite u_small by clia; rlia end.
    - exists lp. split; [regv HR (10%bv:reg); reflexivity | exact Hlp].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma loop_ok : forall k i lp (FPI' : FPState) R M,
    INV i lp FPI' R M -> (n - i <= Z.of_nat k)%Z ->
    runs_to SEGS (mkst (FP:=FPI') R (Z_to_bv 64 0x876c4) M rom) Q.
  Proof using ceil Hev FPI regs mem rom ret sp C data t8 t16 hc n len fs bs ch Hra Hret Hsp Hc Htp Hal32 Hstk Hwst Hwf Hcal Hch HshC Hcar Hn32 Hnr H8 H16 Hsome Hdok Hdar Henv Hhdr Hfsw.
    induction k as [|k IH]; intros i lp FPI' R M HINV Hk.
    { exfalso. destruct HINV as (_ & _ & Hi). rlia. }
    pose proof (u64_range sp) as Hspr. pose proof (u64_range C) as HCr.
    pose proof placement as (F1 & F2 & F3 & G1 & G2 & G3 & G4 & G5 & FF & AA & B1 & B2). pose proof quotients as HQ. hide HQ. hide FF. clear AA.
    pose proof Hhdr as (_ & _ & _ & Hfslo & Hfshi & Hfsal). pose proof Hstk as [St1 St2]. pose proof Hch as [C1 C2]. pose proof Hcar as [A1 A2]. app_facts.
    unfold FITLIN_D, AS_SB, FS_SIZE, FS_FRAMES0, FS_FRAMES_LEN, FS_FLAGS0, FS_FLAGS0_LEN, FS_FRAMES5, FS_HINT0 in *.
    (* [comment removed for export] *)
    assert (JOIN : forall (FPJ : FPState) RJ MJ, INV i lp FPJ RJ MJ ->
              runs_to SEGS (mkst (FP:=FPJ) RJ (Z_to_bv 64 0x87724) MJ rom) Q).
    { intros FPJ RJ MJ HJ.
      pose proof HJ as ((HRF & R19 & Hlp & HMF & HWF & HWC) & R24 & Hi).
      destruct (pack_I _ _ _ _ _ HJ) as (wf & wc & HR & HF & HK & H64 & H96).
      pose proof (H64 : id _) as H64i. pose proof (H96 : id _) as H96i. clear H64 H96.
      (* [comment removed for export] *)
      run_fp 100%nat (@nil Z) noscr true; subst_triv.
      Ltac latch IH i lp' H64i H96i :=
        let Hl := fresh "Hl" in
        branch_case as Hl; norm_latch Hl;
        [ (* [comment removed for export] *)
          eapply (IH (i + 1)%Z lp'); [prove_INV H64i H96i | rlia]
        | (* [comment removed for export] *)
          run_fp 5%nat [0x87778%Z] noscr false; apply (tail_ok lp'); prove_TINV H64i H96i ].
      branch_case as Hj1.
      - latch IH i lp H64i H96i.
      - run_fp 100%nat (@nil Z) noscr true; subst_triv.
        branch_case as Hj2.
        + latch IH i lp H64i H96i.
        + run_fp 100%nat [0x87754%Z] noscr true; subst_triv. frame_store_c.
          latch IH i (i + 1)%Z H64i H96i. }
    (* [comment removed for export] *)
    pose proof HINV as ((HRF & R19 & Hlp & HMF & HWF & HWC) & R24 & Hi).
    destruct (pack_I _ _ _ _ _ HINV) as (wf & wc & HR & HF & HK & H64 & H96).
    pose proof (H64 : id _) as H64i. pose proof (H96 : id _) as H96i. clear H64 H96.
    pose proof HMF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & MFT).
    run_fp 100%nat [0x80f60%Z] noscr true; subst_triv.
    call_ec 0x876d8%Z MFT (EVar 66) (EVar 74) (EVar 128) (EVar 129) (EVar 130).
    run_fp 100%nat (@nil Z) noscr true; subst_triv.
    branch_case as Hc1; [apply (tail_ok lp); prove_TINV H64i H96i|].
    run_fp 100%nat (@nil Z) noscr true; subst_triv.
    branch_case as Hc2; [apply (tail_ok lp); prove_TINV H64i H96i|].
    run_fp 100%nat (@nil Z) noscr true; subst_triv.
    branch_case as Hc3;
      (run_fp 100%nat [0x87724%Z] noscr true; subst_triv; branch_case as Hc4;
       [ apply JOIN; prove_INV H64i H96i
       | run_fp 100%nat [0x87724%Z] noscr true; subst_triv; apply JOIN; prove_INV H64i H96i ]).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition knA : list kentry :=
    [lit8 0x9f920 0xa79b8; lit8 0xa79b8 SB; lit8 0x9f978 0xa79c0; KWord (SA (ELit 0) 0xa79c0) 4 (ELit 1);
     KAlign (EVar 2) 32; KRange (EVar 2) (AS_STKLO + 432) (2 ^ 47 - 24); KWr (SA (EVar 2) (-432)) 456;
     KRange (EVar 64) 2 (2 ^ 24);
     KAlign (EVar 10) 8; KRange (EVar 10) 1 (2 ^ 47 - 32);
     KZero (SA (EAlu ALU_SRL (EVar 10) (ELit 3)) SB) (ELit 3);
     KWord (SA (EVar 10) 0) 4 (EVar 64); KWord (SA (EVar 10) 8) 8 (EVar 65); KWord (SA (EVar 10) 16) 8 (EVar 66);
     KAlign (EVar 67) 64; KRange (EVar 67) 1 (2 ^ 47 - 64); KWr (SA (EVar 67) 32) 4;
     KWord (SA (EAlu ALU_SRL (EVar 67) (ELit 3)) (SB + 4)) 1 (ELit 4);
     KZero (SA (EAlu ALU_SRL (EVar 2) (ELit 3)) (SB + 2)) (ELit 1);
     KWord (SA (EVar 2) 20) 4 (EVar 71);
     KRange (EVar 68) 1 (2 ^ 47 - 8);
     KAlign (EVar 69) 64; KRange (EVar 69) 1 (2 ^ 47 - 64); KRange (EVar 70) 1 (2 ^ 47 - 1);
     KDisj (SA (EVar 67) 0) 64 (SA (EVar 10) 0) 32; KDisj (SA (EVar 69) 0) 64 (SA (EVar 10) 0) 32;
     KDisj (SA (EVar 70) 0) 1 (SA (EVar 10) 0) 32; KDisj (SA (EVar 68) 0) 8 (SA (EVar 10) 0) 32;
     KDisj (SA (EVar 69) 0) 64 (SA (EVar 67) 0) 64; KDisj (SA (EVar 70) 0) 1 (SA (EVar 67) 0) 64;
     KDisj (SA (EVar 68) 0) 8 (SA (EVar 67) 0) 64; KDisj (SA (EVar 69) 0) 64 (SA (EVar 68) 0) 8;
     KDisj (SA (EVar 70) 0) 1 (SA (EVar 68) 0) 8; KDisj (SA (EVar 69) 0) 64 (SA (EVar 70) 0) 1;
     KDisj (SA (EAlu ALU_SRL (EVar 69) (ELit 3)) SB) 8 (SA (EAlu ALU_SRL (EVar 10) (ELit 3)) SB) 3;
     KDisj (SA (EAlu ALU_SRL (EVar 69) (ELit 3)) SB) 8 (SA (EAlu ALU_SRL (EVar 67) (ELit 3)) (SB + 4)) 1;
     KDisj (SA (EAlu ALU_SRL (EVar 67) (ELit 3)) (SB + 4)) 1 (SA (EAlu ALU_SRL (EVar 10) (ELit 3)) SB) 3;
     (* [comment removed for export] *)
     KDisj (SA (EVar 10) 0) 32 ZSH ZSHL; KDisj (SA (EVar 10) 0) 32 ZIMG ZIMGL; KDisj (SA (EVar 10) 0) 32 (SA (EVar 2) (-432)) 464;
     KDisj (SA (EVar 67) 0) 64 ZSH ZSHL; KDisj (SA (EVar 67) 0) 64 ZIMG ZIMGL; KDisj (SA (EVar 67) 0) 64 (SA (EVar 2) (-432)) 464;
     KDisj (SA (EVar 68) 0) 8 ZSH ZSHL; KDisj (SA (EVar 68) 0) 8 ZIMG ZIMGL; KDisj (SA (EVar 68) 0) 8 (SA (EVar 2) (-432)) 464;
     KDisj (SA (EVar 69) 0) 64 ZSH ZSHL; KDisj (SA (EVar 69) 0) 64 ZIMG ZIMGL; KDisj (SA (EVar 69) 0) 64 (SA (EVar 2) (-432)) 464;
     KDisj (SA (EVar 70) 0) 1 ZSH ZSHL; KDisj (SA (EVar 70) 0) 1 ZIMG ZIMGL; KDisj (SA (EVar 70) 0) 1 (SA (EVar 2) (-432)) 464].


  Lemma knA_ok : forall wc0, cell SEGS mem (S + 20) 4 wc0 ->
    let E := Env (vals_ev (junk_vals regs ++ fjunk_vals fp0 ++ [Z_to_bv 64 n; t8; t16; Z_to_bv 64 Fc; Z_to_bv 64 fs; Z_to_bv 64 Ff; Z_to_bv 64 faf; wc0]))
                 (blobs_ev [bs]) in
    know_ok SEGS E mem knA.
  Proof using ceil FPI regs mem sp C data t8 t16 hc n len fs bs ch Hsp Hc Hal32 Hstk Hwst Hshc Hwf Hsf Hcal Hch HshC Hcar Hn32 Hn Ht8 Ht16 Hnr Hdok Henv Hhdr.
    intros wc0 Hwc0 E.
    clear Hdar H8 H16 Hsome Hflags Hev Hsm Hcw.
    unfold knA, lit8. pose proof (u64_range C). pose proof (u64_range sp).
    pose proof placement as (F1 & F2 & F3 & G1 & G2 & G3 & G4 & G5 & FF & AA & B1 & B2). pose proof quotients as HQ. hide HQ.
    destruct Hhdr as (_ & _ & _ & Hlo & Hhi & Hal). destruct Hstk as [St1 St2]. destruct Hch as [C1 C2]. destruct Hcar as [A1 A2]. app_facts.
    unfold FITLIN_D, AS_SB, FS_SIZE, FS_FRAMES0, FS_FRAMES_LEN, FS_FLAGS0, FS_FLAGS0_LEN, FS_FRAMES5 in *.
    destruct Hwst as (_ & _ & _ & W4). destruct Hwf as (_ & _ & _ & V4).
    destruct Henv as (Hcells & _ & _ & _). pose proof (both_cells64 SEGS mem Hcells) as CC.
    destruct CC as (E1 & E2 & E3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & E22 & _).
    unfold acell in E1, E2, E3, E22, Hsf. unfold cell in Hwc0. clear AA. opaque_lets.
    unfold know_ok.
    repeat lazymatch goal with |- Forall _ (_ :: _) => constructor | |- Forall _ [] => constructor end.
    all: lazymatch goal with |- Forall _ _ => fail | _ => idtac end.
    - klitA E E1. - klitA E E2. - klitA E E3. - klitA E E22.
    - apply kalign_intro; [rlia|]. cbn [edenot]; ev_simpl E. rewrite Hsp. exact Hal32.
    - apply krange_intro. cbn [edenot]; ev_simpl E. rewrite Hsp. fold S. rlia.
    - apply (kwr_intro SEGS E mem (EVar 2) sp (-432) 456); [cbn [edenot]; ev_simpl E; exact Hsp | fold S; rlia | rlia | fold S; rlia |].
      fold S. replace (S + -432)%Z with (S - 432)%Z by rlia. exact W4.
    - apply krange_intro. cbn [edenot]; ev_simpl E. rewrite u_small by clia. rlia.
    - apply kalign_intro; [rlia|]. cbn [edenot]; ev_simpl E. rewrite Hc. exact Hcal.
    - apply krange_intro. cbn [edenot]; ev_simpl E. rewrite Hc. rlia.
    - eapply (kzero_shz_intro SEGS E mem (EVar 10) C 3); [cbn [edenot]; ev_simpl E; exact Hc | exact HshC | rlia | rlia].
    - eapply (kword_intro SEGS E mem (EVar 10) C 0 4 (EVar 64) (Z_to_bv 64 n)); cbn; try rlia; auto.
    - eapply (kword_intro SEGS E mem (EVar 10) C 8 8 (EVar 65) t8); cbn; try rlia; auto.
    - eapply (kword_intro SEGS E mem (EVar 10) C 16 8 (EVar 66) t16); cbn; try rlia; auto.
    - apply kalign_intro; [rlia|]. cbn [edenot]; ev_simpl E. rewrite u_small by clia. exact F3.
    - apply krange_intro. cbn [edenot]; ev_simpl E. rewrite u_small by clia. rlia.
    - apply (kwr_intro SEGS E mem (EVar 67) (Z_to_bv 64 Fc) 32 4); [cbn [edenot]; ev_simpl E; reflexivity | rewrite u_small by clia; rlia | rlia | rewrite u_small by clia; rlia |].
      rewrite u_small by clia. exact V4.
    - eapply (kword_intro SEGS E mem (EAlu ALU_SRL (EVar 67) (ELit 3)) _ (SB + 4) 1 (ELit 4) (Z_to_bv 64 4));
        [reflexivity | cbn [edenot]; ev_simpl E; reflexivity | rlia | rlia | rewrite edenot_srl3; cbn [edenot]; ev_simpl E; rewrite u_small by clia; unfold SB; qlia
        | rewrite edenot_srl3; cbn [edenot]; ev_simpl E; rewrite u_small by clia; unfold SB; qlia |].
      rewrite edenot_srl3. cbn [edenot]; ev_simpl E. rewrite u_small by clia. rewrite div8_Fc32 in Hsf. unfold SB.
      replace (Fc / 8 + (2147450880 + 4))%Z with (2147450880 + (Fc / 8 + 4))%Z by rlia. exact Hsf.
    - eapply (kzero_shadow_intro SEGS E mem (EVar 2) sp 2 1); [cbn [edenot]; ev_simpl E; exact Hsp | rlia | rlia | fold S; qlia |].
      intros j Hj. fold S. destruct Hshc as [_ Hz]. rewrite div8_S16 in Hz. replace (SB + S / 8 + j)%Z with (SB + (S / 8 + 2) + (j - 2))%Z by rlia. apply Hz. rlia.
    - eapply (kword_intro SEGS E mem (EVar 2) sp 20 4 (EVar 71) wc0); [cbn [edenot]; ev_simpl E; exact Hsp | cbn [edenot]; ev_simpl E; reflexivity | rlia | rlia | fold S; rlia | fold S; rlia | exact Hwc0].
    - apply krange_intro. cbn [edenot]; ev_simpl E. rewrite u_small by clia. rlia.
    - apply kalign_intro; [rlia|]. cbn [edenot]; ev_simpl E. rewrite u_small by clia. exact G3.
    - apply krange_intro. cbn [edenot]; ev_simpl E. rewrite u_small by clia. rlia.
    - apply krange_intro. cbn [edenot]; ev_simpl E. rewrite u_small by clia. rlia.
    - kdisjA E. - kdisjA E. - kdisjA E. - kdisjA E. - kdisjA E. - kdisjA E. - kdisjA E. - kdisjA E. - kdisjA E. - kdisjA E.
    - kdisjA E. - kdisjA E. - kdisjA E.
    - kdisj_place. - kdisj_place. - kdisj_place. - kdisj_place. - kdisj_place.
    - kdisj_place. - kdisj_place. - kdisj_place. - kdisj_place. - kdisj_place.
    - kdisj_place. - kdisj_place. - kdisj_place. - kdisj_place. - kdisj_place.
  Qed.

  Theorem fitlin_runs : runs_to SEGS (mkst (FP:=FPI) regs (Z_to_bv 64 0x874f0) mem rom) Q.
  Proof using ceil Hev Hsm FPI regs mem rom ret sp C data t8 t16 hc n len fs bs ch Hra Hret Hsp Hc H11 H12 H13 H14 Htp Hal32 Hstk Hwst Hshc Hcw Hwf Hsf Hcal Hch HshC Hcar Hn32 Hn Ht8 Ht16 Hnr H8 H16 Hsome Hdok Hdar Henv Hhdr Hfsw Hhint Hflags.
    pose proof (u64_range sp) as Hspr. pose proof (u64_range C) as HCr. pose proof (u64_range data) as Hdr.
    pose proof placement as (F1 & F2 & F3 & G1 & G2 & G3 & G4 & G5 & FF & AA & B1 & B2). pose proof quotients as HQ. hide HQ.
    hide FF. hide AA.
    pose proof Hhdr as (_ & _ & _ & Hfslo & Hfshi & Hfsal). pose proof Hstk as [St1 St2]. pose proof Hch as [C1 C2]. pose proof Hcar as [A1 A2]. app_facts.
    pose proof Hdok as (Hdok0 & Hdh & Hdal & Hshd). pose proof Hdok0 as (Hlen & Hbs & Hdnz & Hdhi & Hblob). pose proof Hdh as [D1 D2].
    unfold FITLIN_D, AS_SB, FS_SIZE, FS_FRAMES0, FS_FRAMES_LEN, FS_FLAGS0, FS_FLAGS0_LEN, FS_FRAMES5, FS_HINT0,
           FS_SHFRAMES_LEN in *.
    destruct Hcw as (wc0 & Hwc0).
    pose proof (knA_ok wc0 Hwc0) as HK. cbv zeta in HK. unfold knA, lit8 in HK.
    opaque_lets.
    set (E := Env (vals_ev (junk_vals regs ++ fjunk_vals fp0 ++ [Z_to_bv 64 n; t8; t16; Z_to_bv 64 Fc; Z_to_bv 64 fs; Z_to_bv 64 Ff; Z_to_bv 64 faf; wc0]))
                 (blobs_ev [bs])) in HK.
    assert (HR : regs_ok E (sr_vars 0) regs) by exact (regs_ok_vars [] regs _ (blobs_ev [bs])).
    assert (HF : fregs_ok E (sfr_vars 32) fp0) by exact (fregs_ok_vars (junk_vals regs) fp0 _ (blobs_ev [bs])).
    pose proof (HR : id _) as HRid. pose proof (HF : id _) as HFid.
    pin_reg HR (4%bv:reg) (ELit TP) by (regv HR (4%bv:reg); exact Htp).
    pin_reg HR (11%bv:reg) (EVar 64) by (regv HR (11%bv:reg); cbn [edenot]; ev_simpl E; exact H11).
    pin_reg HR (12%bv:reg) (EAlu ALU_ADD (EVar 2) (ELit 20)) by (regv HR (12%bv:reg); cbn [edenot]; ev_simpl E; rewrite alu_add_lit, H12, Hsp; reflexivity).
    pin_reg HR (13%bv:reg) (EAlu ALU_ADD (EVar 2) (ELit 16)) by (regv HR (13%bv:reg); cbn [edenot]; ev_simpl E; rewrite alu_add_lit, H13, Hsp; reflexivity).
    pin_reg HR (14%bv:reg) (EAlu ALU_ADD (EVar 67) (ELit 32)) by (regv HR (14%bv:reg); cbn [edenot]; ev_simpl E; rewrite alu_add_lit, H14, u_small by clia; reflexivity).
    (* [comment removed for export] *)
    run_fp 60%nat [0x3c900%Z] noscr true.
    assert (HFR1 : frame_mod mem M [(Z_to_bv 64 (S - 224), 224%Z)]) by (rewrite EQM; frame_of_log [(SA (EVar 2) (-224), 224%Z)]).
    clear EQM HLF.
    eapply rt_call.
    { eapply (Hsm fs h1 ch FPI0 R M rom (Z_to_bv 64 0x87588)).
      - regv HR (1%bv:reg); reflexivity.
      - apply ret_ok_even; rewrite u_small by clia; reflexivity.
      - unfold stkmalloc_pre; cbv zeta; cbn [al_abi as_both aa_tp both_abi];
        unfold sm_frame, sm_flag, sm_pos, FS_FRAMES0, FS_FLAGS0, AS_SB;
        rewrite EFf0, Efaf0; replace (fs + 8 * 0)%Z with (fs + 0)%Z by rlia; change (64 / 8)%Z with 8%Z.
        split; [regv HR (4%bv:reg); reflexivity|].
        split; [eapply (as_env_frame SEGS ceil both_abi fs ch mem M); [exact both_abi_low | ceil_lo | fs_app | exact HFR1 | | exact Henv];
                constructor; [|constructor]; unfold env_safe; cbn [fst snd]; rewrite u_small by clia; rlia|].
        split; [eapply (fs_hdr_frame SEGS ceil both_abi fs mem M); [exact both_abi_low | ceil_lo | exact HFR1 | | | exact Hhdr];
                [constructor; [|constructor]; unfold env_safe; cbn [fst snd]; rewrite u_small by clia; rlia
                | unfold FS_SSL; solve_apart]|].
        split; [eapply acellw_frame; [exact HFR1 | exact Hhint | rlia | rlia | solve_apart]|].
        split; [rewrite (byte_frame mem M _ _ HFR1) by (first [rlia | solve_apart]); rewrite <- Efaf'; unfold FS_FLAGS0;
                apply (Hflags (pos0 h1)); [unfold FS_FLAGS0_LEN; rlia | intros [HX|[]]; pose proof (unhide AA) as AA'; rewrite <- Efaf' in AA'; unfold FS_FLAGS0 in AA'; rlia]|].
        split; [eapply writable_frame; [exact HFR1|exact Whint]|].
        split; [eapply writable_frame; [exact HFR1|exact Wfaf]|].
        split; [eapply writable_frame; [exact HFR1|exact WFf]|].
        split; [eapply writable_frame; [exact HFR1|exact WSFf]|].
        exists (Z_to_bv 64 (S - 224)). split; [regv_lin HR (2%bv:reg); rewrite Hsp; apply (f_equal (Z_to_bv 64)); fold S; rlia|].
        unfold as_frame, stackish. rewrite !u_small by clia.
        split; [rlia|]. split; [replace (S - 224)%Z with (S + (-224))%Z by rlia; apply mod32_16; [exact Hal32|reflexivity]|].
        eapply writable_frame; [exact HFR1|]. eapply writable_sub; [exact Hwst|rlia|rlia|rlia]. }
    cbv beta. intros FPI1 regs1 mem1 (Hkeep & Hfkeep & Hpost).
    unfold stkmalloc_post in Hpost; cbv zeta in Hpost; unfold sm_frame, sm_flag, sm_pos, FS_FRAMES0, FS_FLAGS0, AS_SB in Hpost.
    rewrite EFf0, Efaf0 in Hpost.
    replace (fs + 8 * 0)%Z with (fs + 0)%Z in Hpost by rlia. change (64 / 8)%Z with 8%Z in Hpost.
    replace (Ff + 64 - 8)%Z with (Ff + 56)%Z in Hpost by rlia.
    destruct Hpost as (Ha0 & Hfr & Hh1 & Hfp).
    assert (HR2 : getr R 2 = Z_to_bv 64 (S - 224)) by (regv_lin HR (2%bv:reg); rewrite Hsp; apply (f_equal (Z_to_bv 64)); fold S; rlia).
    rewrite HR2, (u_small (S - 224)) in Hfr by clia. replace (S - 224 - 208)%Z with (S - 432)%Z in Hfr by rlia. clear HR2.
    unfold regs_kept in Hkeep. unfold fregs_kept in Hfkeep. after_call Hkeep Hfkeep FPI1. clear Hkeep Hfkeep.
    kframe HK Hfr [(SA (EVar 2) (-432), 208%Z); (SA (EVar 68) 0, 8%Z); (SA (EVar 70) 0, 1%Z); (SA (EVar 69) 24, 8%Z);
                   (SA (EVar 69) 56, 8%Z); (SA (EAlu ALU_SRL (EVar 69) (ELit 3)) SB, 8%Z)].
    pin_reg HR (10%bv:reg) (EVar 69) by (regv HR (10%bv:reg); cbn [edenot]; ev_simpl_goal; exact Ha0).
    kn_prefix HK [KWr (SA (EVar 69) 0) 64; KWr (SA (EAlu ALU_SRL (EVar 69) (ELit 3)) SB) 8; KWord (SA (EVar 69) 56) 8 (EVar 70); KWr (SA (EVar 70) 0) 1].
    { apply (kwr_intro SEGS _ mem1 (EVar 69) (Z_to_bv 64 Ff) 0 64);
        [cbn [edenot]; ev_simpl_goal; reflexivity | rewrite u_small by clia; rlia | rlia | rewrite u_small by clia; rlia
        | rewrite u_small, Z.add_0_r by rlia; eapply writable_frame; [exact Hfr |]; eapply writable_frame; [exact HFR1 | exact WFf]]. }
    { replace SB with (SB + 0)%Z by rlia; eapply (kwr_shadow_intro SEGS _ mem1 (EVar 69) (Z_to_bv 64 Ff) 0 8);
        [cbn [edenot]; ev_simpl_goal; reflexivity | rlia | rlia | rewrite u_small by clia; qlia
        | rewrite u_small, Z.add_0_r by rlia; unfold SB; eapply writable_frame; [exact Hfr |]; eapply writable_frame; [exact HFR1 | exact WSFf]]. }
    { eapply (kword_intro SEGS _ mem1 (EVar 69) (Z_to_bv 64 Ff) 56 8 (EVar 70) (Z_to_bv 64 faf));
        [cbn [edenot]; ev_simpl_goal; reflexivity | cbn [edenot]; ev_simpl_goal; reflexivity | rlia | rlia
        | rewrite u_small by clia; rlia | rewrite u_small by clia; rlia | rewrite u_small by clia; unfold acell in Hfp; exact Hfp]. }
    { apply (kwr_intro SEGS _ mem1 (EVar 70) (Z_to_bv 64 faf) 0 1);
        [cbn [edenot]; ev_simpl_goal; reflexivity | rewrite u_small by clia; rlia | rlia | rewrite u_small by clia; rlia
        | rewrite u_small, Z.add_0_r by rlia; eapply writable_frame; [exact Hfr |]; eapply writable_frame; [exact HFR1 | exact Wfaf]]. }
    pose proof (frame_mod_trans _ _ _ _ _ HFR1 Hfr) as HFR2. cbn [app] in HFR2. clear Hfr HFR1.
    (* [comment removed for export] *)
    run_fp 60%nat [0x80f60%Z] noscr true.
    assert (HFR3 : frame_mod mem1 M0 [(Z_to_bv 64 Ff, 24%Z); (Z_to_bv 64 (2147450880 + Ff / 8), 8%Z); (Z_to_bv 64 (S - 208), 208%Z); (Z_to_bv 64 (Ff + 32), 4%Z)]).
    { rewrite EQM. frame_of_log [(SA (EVar 69) 0, 24%Z); (SA (EAlu ALU_SRL (EVar 69) (ELit 3)) SB, 8%Z); (SA (EVar 2) (-208), 208%Z); (SA (EVar 69) 32, 4%Z)]. }
    clear EQM HLF.
    assert (HFT3 : frame_mod mem M0 FTGT).
    { eapply frame_FTGT_app; [| exact HFR3 | solve_fincl]. eapply frame_mod_incl; [|exact HFR2]. solve_fincl. }
    call_ec 0x87644%Z HFT3 (EVar 2) (EVar 10) (EVar 64) (EVar 65) (EVar 66).
    assert (HFT4 : frame_mod mem MC FTGT) by (eapply frame_FTGT_app; [exact HFT3 | exact Hfr | solve_fincl]).
    (* [comment removed for export] *)
    run_fp 60%nat [0x876c4%Z] noscr true.
    assert (HFR5 : frame_mod MC M1 [(Z_to_bv 64 (Fc + 32), 4%Z); (Z_to_bv 64 (S - 208), 208%Z)]).
    { rewrite EQM. frame_of_log [(SA (EVar 67) 32, 4%Z); (SA (EVar 2) (-208), 208%Z)]. }
    assert (HFT5 : frame_mod mem M1 FTGT) by (eapply frame_FTGT_app; [exact HFT4 | exact HFR5 | solve_fincl]).
    clear EQM HLF.
    eapply (loop_ok (Z.to_nat (n - 1)) 1 1); [| rewrite Z2Nat.id by rlia; rlia].
    unfold INV, TINV.
    split; [| split; [creg (24%bv:reg) | rlia]].
    split; [prove_regfix HRid HFid|].
    split; [creg (19%bv:reg)|].
    split; [rlia|].
    split.
    { kcell_auto HK (EVar 2) (-8)%Z 8%nat V1. kcell_auto HK (EVar 2) (-16)%Z 8%nat V2. kcell_auto HK (EVar 2) (-24)%Z 8%nat V3.
      kcell_auto HK (EVar 2) (-32)%Z 8%nat V4. kcell_auto HK (EVar 2) (-40)%Z 8%nat V5. kcell_auto HK (EVar 2) (-48)%Z 8%nat V6.
      kcell_auto HK (EVar 2) (-56)%Z 8%nat V7. kcell_auto HK (EVar 2) (-64)%Z 8%nat V8. kcell_auto HK (EVar 2) (-72)%Z 8%nat V9.
      kcell_auto HK (EVar 2) (-80)%Z 8%nat V10. kcell_auto HK (EVar 2) (-88)%Z 8%nat V11. kcell_auto HK (EVar 2) (-96)%Z 8%nat V12.
      kcell_auto HK (EVar 2) (-104)%Z 8%nat V13.
      kcell_auto HK (EVar 2) (-112)%Z 8%nat V14. kcell_auto HK (EVar 2) (-120)%Z 8%nat V15. kcell_auto HK (EVar 2) (-128)%Z 8%nat V16.
      kcell_auto HK (EVar 2) (-136)%Z 8%nat V17. kcell_auto HK (EVar 2) (-144)%Z 8%nat V18.
      kcell_auto HK (EVar 2) (-152)%Z 8%nat P1. kcell_auto HK (EVar 2) (-168)%Z 8%nat P2. kcell_auto HK (EVar 2) (-176)%Z 8%nat P3.
      kcell_auto HK (EVar 2) (-184)%Z 8%nat P4. kcell_auto HK (EVar 2) (-192)%Z 8%nat P5. kcell_auto HK (EVar 2) (-200)%Z 8%nat P6.
      kcell_auto HK (EVar 2) (-208)%Z 8%nat P7.
      rewrite ?alu_add_lit, ?Hsp in P2. fold S in P2.
      kcell HK (EAlu ALU_SRL (EVar 67) (ELit 3)) (SB + 4)%Z 1%nat (ELit 4) Msf.
      kcell_auto HK (EVar 10) 0%Z 4%nat Mn. rewrite ext_val_zx4_lit in Mn by rlia.
      kcell_auto HK (EVar 10) 8%Z 8%nat M8c. kcell_auto HK (EVar 10) 16%Z 8%nat M16c.
      kcell HK (EVar 69) 56%Z 8%nat (EVar 70) Mfp.
      unfold MEMFIX, SAVED, SPILLS, cell64, LibDefs.cell, acell.
      repeat match goal with |- _ /\ _ => split end; try assumption.
      - unfold SB in *. replace (2147450880 + Fc / 8 + 4)%Z with (Fc / 8 + (2147450880 + 4))%Z by rlia. exact Msf.
      - pose proof FTGT_safe as (_ & _ & _ & _ & _ & _ & _ & _ & T9).
        eapply shz_frame; [exact HFT5 | exact Hshc | rlia | rlia | rewrite div8_S16; exact T9].
      - rewrite Z.add_0_r in Mn. exact Mn.
      - (* [comment removed for export] *) unfold acellw. eapply acellw_frame; [exact (frame_mod_trans _ _ _ _ _ HFR3 (frame_mod_trans _ _ _ _ _ Hfr HFR5)) | | rlia | rlia | cbn [app]; solve_apart_q].
        unfold acellw in Hh1. replace (Z_to_bv 64 (bv_unsigned hc + 2)) with (Z_to_bv 64 (bv_unsigned h1 + 1)); [exact Hh1|].
        apply bv_eq. unfold h1. rewrite !u_lit64a. rewrite Zplus_mod_idemp_l. f_equal. rlia. }
    split; [prove_cell (EVar 67) 32%Z | prove_cell (EVar 2) 20%Z].
  Qed.
End Proof.

Theorem fit_linear_both : forall ceil,
  eval_curve_contract_as SEGS as_both ceil -> stkmalloc0_contract SEGS as_both ceil -> fit_linear_contract_bo SEGS as_both ceil.
Proof.
  intros ceil Hev Hsm data len bs sp C n t8 t16 fs hc ch FPI regs mem rom ret Hra Hret PRE.
  unfold fitlin_pre_bo in PRE. cbv zeta in PRE. cbn [al_abi as_both aa_tp both_abi] in PRE.
  destruct PRE as (Hsp & Hc & H11 & H12 & H13 & H14 & Htp & Hal32 & Hstk & Hwst & Hshc & Hcw & Hwf & Hsf & Hcal & Hch & HshC & Har1 & Har2 &
                   ([Hn32 Hn] & Ht8 & Ht16 & Hnr & H8 & H16 & Hsome) & Hdok & Hdar & Henv & Hhdr & Hfsw & Hhint & Hflags).
  unfold cell64, LibDefs.cell in Ht8, Ht16. unfold LibDefs.cell in Hn.
  apply runs_to_contract.
  eapply runs_to_mono; [| exact (fitlin_runs ceil Hev Hsm FPI regs mem rom ret sp C data t8 t16 hc n len fs bs ch Hra Hret Hsp Hc H11 H12 H13 H14 Htp
                                  Hal32 Hstk Hwst Hshc Hcw Hwf Hsf Hcal Hch HshC (conj Har1 Har2) Hn32 ltac:(rewrite Z.add_0_r; exact Hn) Ht8 Ht16 Hnr
                                  (Hide H8) (Hide H16) (Hide Hsome) Hdok (Hide Hdar) Henv Hhdr Hfsw Hhint Hflags)].
  intros st' (FPI' & regs' & mem' & -> & K1 & K2 & P). exists FPI', regs', mem'.
  split; [reflexivity|]. split; [exact K1|]. split; [exact K2|].
  unfold fitlin_post_bo. cbv zeta. exact P.
Qed.
