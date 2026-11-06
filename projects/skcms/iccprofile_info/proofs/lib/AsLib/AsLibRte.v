(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.skcms.iccprofile_info.images Require Import Asan.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import PropExec CatExec CatSim SeqExec StoreOk SymExec Hoare Frame PropExecFP.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import LibDefs.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.AsLib Require Import AsSymExec AsSymExecSound AsSymRun AsSymDrive AsSymCall AsFuzzContract AsLibShadow AsLibDefs AsLibWP1Spec AsLibPlace.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.AsLib Require Import AsSymDriveLZ.
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
Local Ltac el_lia_core := first [ el_t1 | ((progress el_dm); el_t1) ].
Local Ltac el_goal_has_var := match goal with |- ?G => match G with context [?x] => is_var x end end.
Local Ltac Lia.lia ::= tryif el_goal_has_var then el_lia_core else first [ solve [clear; el_lia_core] | el_lia_core ].
Import ListNotations.
Open Scope bv_scope.
Import ASX. Import ASXS.
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

#[local] Abbreviation SEGS := Asan.M.loaded_segments.

Section RTE.
  Variable ceil : Z.
  Variables (FPI : FPState) (regs : bvmap 5 word) (mem rom : word -> option byte).
  Variables (ret sp c data t8 t16 : word) (n len : Z) (bs : list byte).

  Hypothesis Hra : getr regs 1 = ret.
  Hypothesis Hret : ret_ok ret.
  Hypothesis Hsp : getr regs 2 = sp.
  Hypothesis Hc : getr regs 10 = c.
  Hypothesis Hn   : rdn SEGS mem (Z_to_bv 64 (bv_unsigned c + 0)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 n)).
  Hypothesis Ht8  : rdn SEGS mem (Z_to_bv 64 (bv_unsigned c + 8)) 8 = Some (word_to_le_bytes 8 t8).
  Hypothesis Ht16 : rdn SEGS mem (Z_to_bv 64 (bv_unsigned c + 16)) 8 = Some (word_to_le_bytes 8 t16).
  Hypothesis Hcal : (bv_unsigned c mod 8 = 0)%Z.
  Hypothesis Hcrange : (appm (bv_unsigned c) 24 /\ (0 < bv_unsigned c)%Z) /\ (bv_unsigned c + 24 <= ceil)%Z.
  Hypothesis Hlen : (0 <= len < 2 ^ 26)%Z.
  Hypothesis Hbs : Z.of_nat (length bs) = len.
  Hypothesis Hdrange : (appm (bv_unsigned data) len /\ (0 < bv_unsigned data)%Z) /\ (bv_unsigned data + len <= ceil)%Z.
  Hypothesis Hblob : forall i, (0 <= i < len)%Z ->
      mem (Z_to_bv 64 (bv_unsigned data + i)) = Some (nth (Z.to_nat i) bs (Z_to_bv 8 0)).
  Hypothesis Hcurve : n = 0%Z \/
     ((2 <= n <= 2 ^ 24)%Z
      /\ (bv_unsigned t8 <> 0%Z -> bv_unsigned data <= bv_unsigned t8 /\ bv_unsigned t8 + n <= bv_unsigned data + len)%Z
      /\ (bv_unsigned t16 <> 0%Z -> bv_unsigned data <= bv_unsigned t16 /\ bv_unsigned t16 + 2 * n <= bv_unsigned data + len)%Z).
  (* [comment removed for export] *)
  Hypothesis Hsprange : ((AS_STKLO <= ceil)%Z /\ (ceil + 16 <= bv_unsigned sp)%Z) /\ (bv_unsigned sp <= 2 ^ 47)%Z.
  Hypothesis Hstk : RiscvSemantics.store_ok SEGS mem (Z_to_bv 64 (bv_unsigned sp - 16)) 16 = true.
  Hypothesis Hsb : sbcell SEGS 0x9eaf0 0xa6bb8 mem.
  Hypothesis Hshc : shz mem (bv_unsigned c) 3.
  Hypothesis Hshd : shdata mem (bv_unsigned data) len.

  Let E : env := Env (vals_ev (junk_vals regs ++ fjunk_vals (fp_regs (FPState:=FPI))
                                ++ [Z_to_bv 64 n; t8; t16; data; Z_to_bv 64 len])) (blobs_ev [bs]).

  Definition kn0v1 : list kentry :=
    [KWord (SA (ELit 0) 0x9eaf0) 8 (ELit 0xa6bb8); KWord (SA (ELit 0) 0xa6bb8) 8 (ELit SB);
     KWord (SA (EVar 10) 0) 4 (EVar 64); KWord (SA (EVar 10) 8) 8 (EVar 65); KWord (SA (EVar 10) 16) 8 (EVar 66);
     KAlign (EVar 10) 8; KRange (EVar 10) 1 (2 ^ 47 - 24);
     KRange (EVar 2) (AS_STKLO + 16) (2 ^ 47); KWr (SA (EVar 2) (-16)) 16;
     KZero (SA (EAlu ALU_SRL (EVar 10) (ELit 3)) SB) (ELit 3);
     KRange (EVar 67) 1 (2 ^ 47 - 16); KRange (EVar 68) 0 (2 ^ 26);
     KShad (EVar 67) (EVar 68) SB;
     KBlobD (SA (EVar 67) 0) (EVar 68) 0].

  Lemma kn0v1_ok : know_ok SEGS E mem kn0v1.
  Proof using ceil FPI regs mem sp c data t8 t16 n len bs Hsp Hc Hn Ht8 Ht16 Hcal Hcrange Hlen Hbs Hdrange Hblob Hsprange Hstk Hsb Hshc Hshd.
    unfold kn0v1. pose proof (u64_range c). pose proof (u64_range data). pose proof (u64_range sp).
    destruct Hsb as [Hg Hs]. unfold cell64, cell in Hg, Hs.
    unfold know_ok. repeat lazymatch goal with |- Forall _ (_ :: _) => constructor | |- Forall _ [] => constructor end.
    all: lazymatch goal with |- Forall _ _ => fail | _ => idtac end.
    - eapply (kword_intro SEGS E mem (ELit 0) (Z_to_bv 64 0) 0x9eaf0 8 (ELit 0xa6bb8) (Z_to_bv 64 0xa6bb8)); cbn; rewrite ?u_lit0; cbn; try lia; auto.
    - eapply (kword_intro SEGS E mem (ELit 0) (Z_to_bv 64 0) 0xa6bb8 8 (ELit SB) (Z_to_bv 64 SB)); cbn; rewrite ?u_lit0; cbn; try lia; auto.
    - eapply (kword_intro SEGS E mem (EVar 10) c 0 4 (EVar 64) (Z_to_bv 64 n)); cbn; try lia; auto.
    - eapply (kword_intro SEGS E mem (EVar 10) c 8 8 (EVar 65) t8); cbn; try lia; auto.
    - eapply (kword_intro SEGS E mem (EVar 10) c 16 8 (EVar 66) t16); cbn; try lia; auto.
    - apply kalign_intro; [lia|]. cbn. rewrite Hc. exact Hcal.
    - apply krange_intro. cbn. rewrite Hc. lia.
    - apply krange_intro. cbn. rewrite Hsp. lia.
    - apply (kwr_intro SEGS E mem (EVar 2) sp (-16) 16); cbn; try lia; auto.
    - eapply (kzero_shz_intro SEGS E mem (EVar 10) c 3); [cbn; exact Hc | exact Hshc | lia | lia].
    - apply krange_intro. cbn. lia.
    - apply krange_intro. cbn. rewrite u_small by lia. lia.
    - eapply (kshad_intro SEGS E mem (EVar 67) (EVar 68) data len); [reflexivity | cbn; rewrite u_small by lia; reflexivity | lia | lia | exact Hshd].
    - cbn [kentry_ok]. unfold flat, estart, elenZ. cbn. rewrite u_small by lia.
      split; [lia|]. split; [exact Hbs|]. intros i Hi. rewrite Z.add_0_r. apply Hblob. exact Hi.
  Qed.

  Definition kn0 : list kentry := kn0v1 ++
    [KRange (EAlu ALU_ADD (EVar 67) (EVar 68)) 0 (2 ^ 47 - 16);
     KDisj (SA (EVar 10) 0) 24 ZSH ZSHL; KDisj (SA (EVar 10) 0) 24 ZIMG ZIMGL;
     KDisj (SA (EVar 10) 0) 24 (SA (EVar 2) (-16)) 16].
  Lemma kn0_ok : know_ok SEGS E mem kn0.
  Proof using ceil FPI regs mem sp c data t8 t16 n len bs Hsp Hc Hn Ht8 Ht16 Hcal Hcrange Hlen Hbs Hdrange Hblob Hsprange Hstk Hsb Hshc Hshd. apply know_ok_app; [exact kn0v1_ok | kn_place]. Qed.

  Definition RS : list (saddr * Z) := [(SA (EVar 2) (-16), 16%Z)].
  Lemma RS_denot : regions_denot E RS = [(Z_to_bv 64 (bv_unsigned sp - 16), 16%Z)].
  Proof using FPI regs sp data t8 t16 n len bs Hsp.
    unfold regions_denot, RS. cbn [map fst snd]. unfold adenot. cbn [a_base a_off edenot]. ev_simpl E.
    rewrite Hsp. unfold v_addi. reflexivity.
  Qed.

  Ltac post :=
    lazymatch goal with
    | |- exists FPI' regs' mem', @mkst ?FPI ?R _ ?M _ = _ /\ _ =>
      lazymatch goal with
      | HR : regs_ok ?E _ R, HF : fregs_ok _ _ (@fp_regs FPI), HR0 : id (regs_ok _ ?sr0 ?regs), HF0 : id (fregs_ok _ ?sfr0 ?fr),
        EQM : M = mem_denot _ ?M0 ?log |- _ =>
        exists FPI, R, M; split; [| split; [|split]]; unfold regs_kept, fregs_kept;
        [ regv HR (1%bv:reg); rewrite_getr; reflexivity
        | eapply (regs_same_on E sr0 _ regs R abi_kept); [ exact HR0 | exact HR | vm_compute; reflexivity ]
        | eapply (fregs_same_on E sfr0 _ fr _ abi_fkept); [ exact HF0 | exact HF | vm_compute; reflexivity ]
        | rewrite EQM, <- RS_denot; apply (frame_mod_mem_denot E M0 log RS);
          [ assumption | flats_auto | vm_compute; reflexivity ] ]
      end
    end.

  Theorem rte_run_ok :
    exists (FPI' : FPState) regs' mem',
      msteps SEGS (mkst (FP:=FPI) regs (Z_to_bv 64 0x80328) mem rom)
                  (mkst (FP:=FPI') regs' ret mem' rom)
      /\ regs_kept abi_kept regs regs'
      /\ fregs_kept abi_fkept (fp_regs (FPState:=FPI)) (fp_regs (FPState:=FPI'))
      /\ frame_mod mem mem' [(Z_to_bv 64 (bv_unsigned sp - 16), 16%Z)].
  Proof using ceil FPI regs mem rom ret sp c data t8 t16 n len bs Hra Hret Hsp Hc Hn Ht8 Ht16 Hcal Hcrange Hlen Hbs Hdrange Hblob Hcurve Hsprange Hstk Hsb Hshc Hshd.
    apply runs_to_contract with
      (P := fun FPI' regs' mem' => regs_kept abi_kept regs regs'
              /\ fregs_kept abi_fkept (fp_regs (FPState:=FPI)) (fp_regs (FPState:=FPI')) /\
              frame_mod mem mem' [(Z_to_bv 64 (bv_unsigned sp - 16), 16%Z)]).
    assert (HR : regs_ok E (sr_vars 0) regs) by exact (regs_ok_vars [] regs _ (blobs_ev [bs])).
    assert (HF : fregs_ok E (sfr_vars 32) fp_regs) by exact (fregs_ok_vars (junk_vals regs) fp_regs _ (blobs_ev [bs])).
    pose proof (HR : id _) as HR0. pose proof (HF : id _) as HF0.
    pose proof (u64_range t8). pose proof (u64_range t16). pose proof (u64_range data).
    destruct Hcurve as [Hn0 | (Hnr & H8 & H16)].
    - (* [comment removed for export] *)
      assert (HK : know_ok SEGS E mem (KRange (EVar 64) 0 0 :: kn0)).
      { constructor; [apply krange_intro; cbn; subst n; rewrite u_small by lia; lia | apply kn0_ok]. }
      run_fp 120%nat (@nil Z) noscr true. fin_ret. post.
    - (* [comment removed for export] *)
      assert (K64 : kentry_ok SEGS E mem (KRange (EVar 64) 2 (2^24))).
      { apply krange_intro; cbn; rewrite u_small by lia; lia. }
      assert (Kcase : forall (i : nat) (t : word) (z : {bv_unsigned t = 0%Z} + {bv_unsigned t <> 0%Z}),
                edenot E (EVar i) = t ->
                (bv_unsigned t <> 0%Z -> 1 <= bv_unsigned t /\ bv_unsigned t <= 2 ^ 47 - 16)%Z ->
                kentry_ok SEGS E mem (if z then KRange (EVar i) 0 0 else KRange (EVar i) 1 (2 ^ 47 - 16))).
      { intros i t z Hi Hb. pose proof (u64_range t). destruct z; apply krange_intro; rewrite Hi; [lia|].
        specialize (Hb ltac:(assumption)). lia. }
      pose proof (Kcase 65%nat t8 (Z.eq_dec (bv_unsigned t8) 0) eq_refl ltac:(intros Hz; specialize (H8 Hz); lia)) as K65.
      pose proof (Kcase 66%nat t16 (Z.eq_dec (bv_unsigned t16) 0) eq_refl ltac:(intros Hz; specialize (H16 Hz); lia)) as K66.
      assert (HK : know_ok SEGS E mem
               (KRange (EVar 64) 2 (2^24)
                :: (if Z.eq_dec (bv_unsigned t8) 0 then KRange (EVar 65) 0 0 else KRange (EVar 65) 1 (2 ^ 47 - 16))
                :: (if Z.eq_dec (bv_unsigned t16) 0 then KRange (EVar 66) 0 0 else KRange (EVar 66) 1 (2 ^ 47 - 16))
                :: kn0)).
      { constructor; [exact K64|]. constructor; [exact K65|]. constructor; [exact K66|]. apply kn0_ok. }
      clear K64 K65 K66 Kcase.
      destruct (Z.eq_dec (bv_unsigned t8) 0) as [Ht8z | Ht8nz];
        [| specialize (H8 Ht8nz)];
      destruct (Z.eq_dec (bv_unsigned t16) 0) as [Ht16z | Ht16nz];
        try specialize (H16 Ht16nz);
      run_fp 120%nat (@nil Z) noscr true; fin_ret; post.
  Qed.
End RTE.

(* [comment removed for export] *)
Theorem rte_as_ok : forall ceil, rte_contract_as SEGS as_asan ceil.
Proof.
  intros ceil data len bs c FPI regs mem rom ret Hra Hret PRE.
  destruct PRE as (Hc & ((Hlen & Hbs & Hdnz & Hdata & Hblob) & Hheap & Hdal & Hshd) & Hcurve & Hal & Hcheap & Hshc & Hsb & (sp & Hsp & Hfr)).
  destruct Hcurve as (n & t8 & t16 & [Hn32 Hn] & H8c & H16c & Hcv).
  unfold cell64, cell in H8c, H16c. unfold cell in Hn.
  apply (as_sb_asan SEGS mem) in Hsb.
  destruct Hfr as ([Hst1 Hst2] & Hsal & (_ & _ & _ & Hwr)).
  unfold heapish in *. app_facts.
  destruct (rte_run_ok ceil FPI regs mem rom ret sp c data t8 t16 n len bs Hra Hret Hsp Hc
              ltac:(rewrite Z.add_0_r; exact Hn) H8c H16c Hal ltac:(plc) Hlen Hbs ltac:(plc) Hblob
              ltac:(destruct Hcv as [Hz | (Hr & Hnz & H8 & H16)]; [left; exact Hz | right];
                    split; [exact Hr|]; split;
                    [ intros Hz; destruct (H8 Hz) as (A & _ & B); split; [exact A|exact B]
                    | intros Hz; destruct (H16 Hz) as (A & _ & B); split; [exact A|exact B] ])
              ltac:(plc) Hwr Hsb Hshc Hshd)
    as (FPI' & regs' & mem' & Hms & Hk1 & Hk2 & Hmem).
  exists FPI', regs', mem'. unfold rte_post_as. rewrite Hsp. auto.
Qed.
