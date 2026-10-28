(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Sorting.Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec CellsX TacX Frame SFModel.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsIfaceX AsCXXHeap AsCall AsCallX ECH_AImg ECH_Xpres ECH_ARep ECH_ALib ECH_Iface
  ECH_AStmt_C1 ECH_AStmt_C5 ECH_AStmt_C10 ECH_AStmt_C13 ECH_AKit ECH_AsKit ECH_AsKitK ECH_AC14_decexts_seg ECH_AC14_fcc_seg ECH_AC14_bio2buf_seg ECH_AC14_entryK.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import N6_tac.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import StoreDj.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition ADE_AHEAD : Z := 0x553908.  Definition ADE_R0 : Z := 0x55392c.   Definition ADE_R1 : Z := 0x553940.   Definition ADE_J1 : Z := 0x553a44.
Definition ADE_SKIP : Z := 0x553da4.   Definition ADE_SK_R1 : Z := 0x553db4. Definition ADE_SK_R2 : Z := 0x553dc4.
Definition ADE_R2 : Z := 0x553b98.     Definition ADE_R3 : Z := 0x553c08.   Definition ADE_LH : Z := 0x553c4c.   Definition ADE_J2 : Z := 0x553ddc.
Definition ADE_R4 : Z := 0x51af40.     Definition ADE_R5 : Z := 0x553e58.   Definition ADE_R6 : Z := 0x553e80.   Definition ADE_J3 : Z := 0x553e84.
Definition ADE_R7 : Z := 0x553ec8.     Definition ADE_OK : Z := 0x553fc8.   Definition ADE_R8 : Z := 0x553fd4.   Definition ADE_R9 : Z := 0x554008.
Definition ADE_R10 : Z := 0x55401c.    Definition ADE_R11 : Z := 0x554054.  Definition ADE_R12 : Z := 0x55406c.  Definition ADE_R13 : Z := 0x554080.
Definition ADE_R14 : Z := 0x554094.    Definition ADE_PUSH : Z := 0x5540a8. Definition ADE_R15 : Z := 0x5540b4.  Definition ADE_ADV : Z := 0x5540c0.
Definition ADE_TA : Z := 0x5541b0.     Definition ADE_TZ : Z := 0x5541e8.   Definition ADE_TX : Z := 0x554230.   Definition ADE_TX2 : Z := 0x554268.
Definition ADE_FCCFAIL : Z := 0x51b47c. Definition ADE_A367 : Z := 0x51b474. Definition ADE_A447 : Z := 0x51b4a0.
Definition ADE_F538 : Z := 0x554308.   Definition ADE_F534 : Z := 0x554320.
(* [comment removed for export] *)
Definition ADE_FILE : Z := 0x11238e.   (* [comment removed for export] *)
Definition AECH_VERSION : Z := 0xfe0d.
Definition ATH_CMP : Z := 0x554544. Definition ATH_COPY : Z := 0x554570. Definition ATH_FREE : Z := 0x55451c.   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition arp_fframe2 (q tpl : Z) (j24 : list byte) (lb : byte) (tpb j128 : list byte) (rb : Z) (j2 : list byte) (fp : Z) : list cell :=
  [C8 (wz AFRAME_MAGIC); C8 (wz ARP_DESCR); C8 (wz P_ech_read_priv_echconfiglist); C8 (wz q); C8 (wz tpl); CB 24 j24; C1 lb; CB 2063 tpb; CB 128 j128;
   C8 (wz rb); CB 1824 j2; C8 (wz fp)].

(* [comment removed for export] *)
Definition upd_version (E : entrep) (v : Z) : entrep :=
  mkENT v (en_pname E) (en_pname_o E) (en_publen E) (en_pub E) (en_pub_o E) (en_nsuites E) (en_suites E) (en_suites_o E)
        (en_maxname E) (en_cfgid E) (en_exts E) (en_exts_o E) (en_loadtime E) (en_forretry E) (en_enclen E) (en_encoded E) (en_encoded_o E) (en_id E).
Definition upd_cfgid (E : entrep) (v : Z) : entrep :=
  mkENT (en_version E) (en_pname E) (en_pname_o E) (en_publen E) (en_pub E) (en_pub_o E) (en_nsuites E) (en_suites E) (en_suites_o E)
        (en_maxname E) v (en_exts E) (en_exts_o E) (en_loadtime E) (en_forretry E) (en_enclen E) (en_encoded E) (en_encoded_o E) (en_id E).
Definition upd_nsuites (E : entrep) (v : Z) : entrep :=
  mkENT (en_version E) (en_pname E) (en_pname_o E) (en_publen E) (en_pub E) (en_pub_o E) v (en_suites E) (en_suites_o E)
        (en_maxname E) (en_cfgid E) (en_exts E) (en_exts_o E) (en_loadtime E) (en_forretry E) (en_enclen E) (en_encoded E) (en_encoded_o E) (en_id E).
Definition upd_suites (E : entrep) (v : Z) (o : oblk) : entrep :=
  mkENT (en_version E) (en_pname E) (en_pname_o E) (en_publen E) (en_pub E) (en_pub_o E) (en_nsuites E) v o
        (en_maxname E) (en_cfgid E) (en_exts E) (en_exts_o E) (en_loadtime E) (en_forretry E) (en_enclen E) (en_encoded E) (en_encoded_o E) (en_id E).
Definition upd_maxname (E : entrep) (v : Z) : entrep :=
  mkENT (en_version E) (en_pname E) (en_pname_o E) (en_publen E) (en_pub E) (en_pub_o E) (en_nsuites E) (en_suites E) (en_suites_o E)
        v (en_cfgid E) (en_exts E) (en_exts_o E) (en_loadtime E) (en_forretry E) (en_enclen E) (en_encoded E) (en_encoded_o E) (en_id E).
Definition upd_enclen (E : entrep) (v : Z) : entrep :=
  mkENT (en_version E) (en_pname E) (en_pname_o E) (en_publen E) (en_pub E) (en_pub_o E) (en_nsuites E) (en_suites E) (en_suites_o E)
        (en_maxname E) (en_cfgid E) (en_exts E) (en_exts_o E) (en_loadtime E) (en_forretry E) v (en_encoded E) (en_encoded_o E) (en_id E).
Definition upd_encoded (E : entrep) (v : Z) (o : oblk) : entrep :=
  mkENT (en_version E) (en_pname E) (en_pname_o E) (en_publen E) (en_pub E) (en_pub_o E) (en_nsuites E) (en_suites E) (en_suites_o E)
        (en_maxname E) (en_cfgid E) (en_exts E) (en_exts_o E) (en_loadtime E) (en_forretry E) (en_enclen E) v o (en_id E).
Definition upd_loadtime (E : entrep) (v : Z) : entrep :=
  mkENT (en_version E) (en_pname E) (en_pname_o E) (en_publen E) (en_pub E) (en_pub_o E) (en_nsuites E) (en_suites E) (en_suites_o E)
        (en_maxname E) (en_cfgid E) (en_exts E) (en_exts_o E) v (en_forretry E) (en_enclen E) (en_encoded E) (en_encoded_o E) (en_id E).
Lemma upd_version_id : forall E, upd_version E (en_version E) = E.   Proof. intros E. destruct E. reflexivity. Qed.
Lemma upd_cfgid_id : forall E, upd_cfgid E (en_cfgid E) = E.         Proof. intros E. destruct E. reflexivity. Qed.
Lemma upd_nsuites_id : forall E, upd_nsuites E (en_nsuites E) = E.   Proof. intros E. destruct E. reflexivity. Qed.
Lemma upd_maxname_id : forall E, upd_maxname E (en_maxname E) = E.   Proof. intros E. destruct E. reflexivity. Qed.
(* [comment removed for export] *)
Definition bz (bs : list byte) (j : nat) : Z := match nth_error bs j with Some b => bv_unsigned b | None => 0 end.
Fixpoint srows (bs : list byte) (off : nat) (kem : Z) (n : nat) : list (Z * Z * Z) :=
  match n with
  | O => []
  | S n' => (kem, 256 * bz bs off + bz bs (S off), 256 * bz bs (S (S off)) + bz bs (S (S (S off)))) :: srows bs (4 + off) kem n'
  end.
Lemma srows_length : forall bs off kem n, length (srows bs off kem n) = n.
Proof. intros bs off kem n. revert off. induction n as [|n IH]; intros off; cbn; [reflexivity| rewrite IH; reflexivity]. Qed.
Lemma bz_range : forall bs j, 0 <= bz bs j < 256.
Proof. intros bs j. unfold bz. destruct (nth_error bs j) as [b|]; [apply abyte_range| lia]. Qed.
Lemma wrap_neg : forall x, - 2^64 <= x < 0 -> bv_unsigned (Z_to_bv 64 x) = x + 2^64.
Proof.
  intros x Hx. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
  rewrite <- (Z.mod_add x 1 (2^64)) by lia. rewrite Z.mod_small by lia. lia.
Qed.
(* [comment removed for export] *)
Fixpoint asuite_cells (rows : list (Z * Z * Z)) : list cell :=
  match rows with [] => [] | (kem, kdf, aead) :: rows' => C2 (wz kem) :: C2 (wz kdf) :: C2 (wz aead) :: asuite_cells rows' end.
Lemma asuite_cells_size : forall rows, Z.of_nat (cells_size (asuite_cells rows)) = 6 * zlength rows.
Proof. unfold zlength. induction rows as [|[[k d] a] rows IH]; cbn [asuite_cells cells_size csize length]; [reflexivity|]. cbn [cells_size csize Nat.add] in IH |- *. lia. Qed.
Lemma mod64_neg : forall x, - 2^64 <= x < 0 -> x mod 2^64 = x + 2^64.
Proof. intros x Hx. rewrite <- (Z.mod_add x 1 (2^64)) by lia. rewrite Z.mod_small by lia. lia. Qed.
(* [comment removed for export] *)
Lemma add_not64 : forall r x, 0 <= x < 2^64 -> Z_to_bv 64 (r + Z.lxor x 18446744073709551615) = Z_to_bv 64 (r - x - 1).
Proof.
  intros r x Hx. rewrite lnot_mod64 by lia. unfold Z.lnot, Z.pred. apply Z_to_bv_eqm.
  rewrite Z.add_mod, Z.mod_mod, <- Z.add_mod by lia. f_equal. lia.
Qed.
(* [comment removed for export] *)
Lemma be16_lor : forall hi lo, 0 <= hi < 256 -> 0 <= lo < 256 -> Z.lor (hi * 2 ^ 8) lo = lo + 256 * hi.
Proof.
  intros hi lo Hh Hl. rewrite Z.lor_comm. replace (hi * 2 ^ 8) with (Z.shiftl hi 8) by (rewrite Z.shiftl_mul_pow2 by lia; reflexivity).
  rewrite (lor_shiftl8_add lo hi) by lia. lia.
Qed.

Section S.
  Context {HCEIL : HeapCeil}.
  Local Ltac kill K := exfalso; revert K; rewrite ?unsigned_lit, ?signed_lit by lia; lia.
  Local Ltac br := let K0 := fresh "K0" in if_cases K0; zify_cond K0; try kill K0; try clear K0.
  Local Ltac retpc := match goal with |- context [ret_pc (Z_to_bv 64 ?v)] => replace (ret_pc (Z_to_bv 64 v)) with (Z_to_bv 64 v) by (symmetry; apply ret_pc_even; [lia| reflexivity]) end.
  (* [comment removed for export] *)
  Local Ltac aland MU1 WM1 :=
    lazymatch type of MU1 with munch ?W1 ?ma ?mb =>
      repeat match goal with
      | Hc : rw_cells asegs ma _ _ |- _ =>
          first [ eapply rw_cells_transport in Hc; [| exact MU1| exact WM1| cbn [cells_size csize Nat.add length disjoint_from fst snd Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul Nat.mul]; lia]
                | clear Hc ]
      | Hb : bytes_at asegs ma _ _ |- _ =>
          first [ eapply bytes_at_transport in Hb; [| exact MU1| exact WM1| cbn [disjoint_from fst snd]; lia] | clear Hb ]
      end;
      lazymatch goal with MU : munch ?W ?m0 ma |- _ =>
        lazymatch goal with WM : wmono asegs m0 ma |- _ =>
          let MU' := fresh "MU" in let WM' := fresh "WM" in
          assert (MU' : munch W m0 mb) by (eapply munch_trans; [exact MU| eapply munch_weaken; [| exact MU1]]; intros z Hz; cbn in Hz |- *; lia);
          pose proof (wmono_trans asegs _ _ _ WM WM1) as WM'; clear MU WM MU1 WM1; rename MU' into MU; rename WM' into WM
        end end end.
  (* [comment removed for export] *)
  Lemma ade_byte : forall m base bs cur i b,
    bytes_at asegs m base bs -> nth_error bs (Z.to_nat (cur - base + i)) = Some b -> base <= cur -> 0 <= i ->
    ov_read_bytes asegs m (wa (cur + i)) 1 = Some [b].
  Proof.
    intros m base bs cur i b BS NTH LE I0. eapply (u8ro_read asegs m base bs (cur - base + i) b); [exact BS| exact NTH| lia|]. f_equal. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma ade_seg1 :
    forall (rax gp tp t0 t1 t2 s0w a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (q ff SH cur rem : Z)
           (w16 w24 w32 w40 w48 w56 w64 w80 w88 w96 w104 w112 w120 w128 : word)
           (w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 : word)
           (tpl rb fp : Z) (j24 : list byte) (lb : byte) (tpb j128 j2 : list byte) (sa : list byte) (sb : byte) (sc : list byte) (sb2 sc2 : byte) (sd se : list byte) (sr : byte) (sg : list byte),
      set_shadow_00_stmt ->
      rw_cells asegs m (q + 16) (arp_sg1 w16 w24 w32 w40 w48 w56 w64 (wz ADE_FILE) w80 w88 w96 w104 w112 w120 w128 (wz (ff + 32))) ->
      rw_cells asegs m (q + 144) (arp_sg2 (wz (SH + 10)) w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232) ->
      rw_cells asegs m ff (arp_fframe2 q tpl j24 lb tpb j128 rb j2 fp) ->
      rw_cells asegs m SH (arp_fshadow sa sb sc sb2 sc2 sd se sr sg) ->
      ASHB + AIMG_TOP / 8 <= SH -> SH + 512 < AHI_LO -> AIMG_TOP + 32 <= ff -> ff + 4096 <= aceil -> aapp ff 4096 ->
      aceil <= q -> q + 344 < 2^64 ->
      mem_inv asegs m -> ACONST m ->
      evt asegs (fun ms' => exists (t0' t1' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m1,
          ms' = MS (mkR (Z_to_bv 64 ADE_R1) (Z_to_bv 64 q) gp tp t0' t1' t2' s0w (Z_to_bv 64 q)
                       (Z_to_bv 64 104) (Z_to_bv 64 ADE_FILE) (Z_to_bv 64 360) a3' a4' a5' a6' a7'
                       (Z_to_bv 64 2) (Z_to_bv 64 SH) s4 s5 s6 (Z_to_bv 64 rem) (Z_to_bv 64 cur) s9 s10 s11 t3' t4' t5' t6')
                   F (Z_to_bv 64 P_CRYPTO_zalloc) fc None m1 (seg_rom asegs)
          /\ munch [(SH + 4, SH + 5); (ff + 32, ff + 40); (SH + 8, SH + 9); (SH + 10, SH + 266)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
          /\ rw_cells asegs m1 ff (arp_fframe2 q 0 j24 lb tpb j128 rb j2 fp)
          /\ rw_cells asegs m1 SH (arp_fshadow sa (b8 0) sc (b8 1) sc2 (poison_bytes 256 0) se sr sg)
          /\ ACONST m1)
        (MS (mkR rax (Z_to_bv 64 q) gp tp t0 t1 t2 s0w (Z_to_bv 64 q) a0 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 2) (Z_to_bv 64 SH) s4 s5 s6 (Z_to_bv 64 rem) (Z_to_bv 64 cur) s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 ADE_AHEAD) fc None m (seg_rom asegs)).
  Proof.
    intros until sg. intros SF00 FA FB FF FS SH1 SH2 FF1 FF2 AAP CQ QH MI AC.
    unfold ADE_AHEAD, ADE_R1, P_CRYPTO_zalloc in *. unfold arp_sg1, arp_sg2, ADE_FILE, wz in FA, FB |- *. unfold arp_fframe2, wz in FF |- *. unfold arp_fshadow in FS |- *.
    acb. unfold aapp, aapp_lo, aapp_hi, AIMG_TOP, AHI_LO, ALOWSH_LO in AAP, FF1.
    let v := eval vm_compute in (AIMG_TOP / 8) in change (AIMG_TOP / 8) with v in SH1.
    unfold ASHB in *. unfold AHI_LO in SH2.
    pose proof (munch_refl [(SH + 4, SH + 5); (ff + 32, ff + 40); (SH + 8, SH + 9); (SH + 10, SH + 266)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    (* [comment removed for export] *)
    go. step.
    (* [comment removed for export] *)
    lazymatch goal with FSx : rw_cells asegs ?mx SH (?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?rest) |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      pose proof FSx as SHC; change (rw_cells asegs mx SH ([c1; c2; c3; c4; c5] ++ (c6 :: rest))) in SHC end.
    apply (proj1 (rw_cells_app _ _ _ _ _)) in SHC. destruct SHC as [SH3 SHR4]. cbn [cells_size csize Nat.add] in SHR4. change (Z.of_nat 10) with 10 in SHR4.
    lazymatch type of SHR4 with rw_cells _ ?mx _ (?c4 :: ?rest) => change (rw_cells asegs mx (SH + 10) ([c4] ++ rest)) in SHR4 end.
    apply (proj1 (rw_cells_app _ _ _ _ _)) in SHR4. destruct SHR4 as [SH256 SHT]. cbn [cells_size csize Nat.add] in SHT. change (Z.of_nat 256) with 256 in SHT.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      assert (ACc : ACONST mc) by
        (eapply ACONST_frame; [exact AC| exact MU| exact WM|];
         apply Forall_cons; [apply aconst_ok_high; cbn [fst snd]; unfold sh, AIMG_TOP; rewrite ?ASHADOW_BASE_val; lia|];
         apply Forall_cons; [eapply aconst_ok_aapp; [exact AAP| cbn; lia| cbn; lia]|];
         apply Forall_cons; [apply aconst_ok_high; cbn [fst snd]; unfold sh, AIMG_TOP; rewrite ?ASHADOW_BASE_val; lia|];
         apply Forall_cons; [apply aconst_ok_high; cbn [fst snd]; unfold sh, AIMG_TOP; rewrite ?ASHADOW_BASE_val; lia| apply Forall_nil]) end.
    eapply evt_cut.
    { unfold set_shadow_00_stmt, set_shadow_stmt in SF00. eapply SF00 with (n := 256); [reflexivity| reflexivity| lia| change (Z.to_nat 256) with 256%nat; exact SH256| assumption| exact ACc]. }
    cbv beta. intros ms1 PO. unfold set_shadow_post in PO.
    destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & mA & -> & MU1 & WM1 & MI1 & SH256').
    retpc. clear SH256.
    aland MU1 WM1.
    (* [comment removed for export] *)
    go. step.
    finish.
    { (* [comment removed for export] *)
      lazymatch goal with |- rw_cells _ ?mx ?base _ =>
        lazymatch goal with A : rw_cells _ mx base [_; _; _; _; _], B : rw_cells _ mx (base + 10) [_], C : rw_cells _ mx (base + 10 + 256) _ |- _ =>
            change (Z.to_nat 256) with 256%nat in B;
            pose proof (proj2 (rw_cells_app asegs mx (base + 10) [CB 256 (poison_bytes 256 0)] _) (conj B ltac:(cbn [cells_size csize Nat.add]; change (Z.of_nat 256) with 256; exact C))) as BC;
            cbn [app] in BC;
            pose proof (proj2 (rw_cells_app asegs mx base _ _) (conj A ltac:(cbn [cells_size csize Nat.add]; change (Z.of_nat 10) with 10; exact BC))) as ABC;
            cbn [app] in ABC; exact ABC end end. }
    eapply ACONST_frame; [exact AC| exact MU| exact WM|].
    apply Forall_cons; [apply aconst_ok_high; cbn [fst snd]; unfold sh, AIMG_TOP; rewrite ?ASHADOW_BASE_val; lia|].
    apply Forall_cons; [eapply aconst_ok_aapp; [exact AAP| cbn; lia| cbn; lia]|].
    apply Forall_cons; [apply aconst_ok_high; cbn [fst snd]; unfold sh, AIMG_TOP; rewrite ?ASHADOW_BASE_val; lia|].
    apply Forall_cons; [apply aconst_ok_high; cbn [fst snd]; unfold sh, AIMG_TOP; rewrite ?ASHADOW_BASE_val; lia| apply Forall_nil].
  Qed.

  (* [comment removed for export] *)
  Lemma ade_seg2 :
    forall (rax gp tp t0 t1 t2 s0w a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (q cur rem Bb blen ee : Z) (bs : list byte) (E : entrep) pad1 pad2 pad3 pad4
           (w16 w24 w32 w40 w48 w56 w72 w80 w96 w104 w112 w120 w128 w136 : word)
           (w144 w152 w160 w168 w184 w192 w200 w208 w216 w224 w232 : word)
           (x240 x248 x256 x264 x272 x280 x288 x296 x304 x312 x320 x328 x336 : word),
      rw_cells asegs m (q + 16) (arp_sg1 w16 w24 w32 w40 w48 w56 (wz AECH_VERSION) w72 w80 (wz Bb) w96 w104 w112 w120 w128 w136) ->
      rw_cells asegs m (q + 144) (arp_sg2 w144 w152 w160 w168 (wz ASHB) w184 w192 w200 w208 w216 w224 w232) ->
      rw_cells asegs m (q + 240) (arp_sg3 x240 x248 x256 x264 x272 x280 x288 x296 x304 x312 x320 x328 x336) ->
      bytes_at asegs m Bb bs -> Bb <= cur -> 1 <= rem -> cur + rem <= Bb + zlength bs -> 0 < Bb -> Bb + zlength bs <= aceil ->
      accessible m Bb blen -> zlength bs <= blen ->
      rw_cells asegs m ee (entry_cells E pad1 pad2 pad3 pad4) -> 0 < ee -> ee mod 16 = 0 -> ee + ENTRY_SIZE <= aceil -> (Bb + zlength bs <= ee \/ ee + ENTRY_SIZE <= Bb) ->
      accessible m ee ENTRY_SIZE -> (ee + ENTRY_SIZE <= ALOWSH_LO \/ AHI_LO <= ee) ->
      aceil <= q -> q + 344 < 2^64 -> mem_inv asegs m ->
      evt asegs (fun ms' => exists (a0' a1' a2' a3' a4' a5' s7' s10' : word) m1 (w48' x320' x328' x336' : word) (v : Z),
          munch [(q + 48, q + 56); (q + 168, q + 176); (q + 320, q + 344); (ee, ee + 2)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
          /\ rw_cells asegs m1 (q + 16) (arp_sg1 w16 w24 w32 w40 w48' w56 (wz AECH_VERSION) w72 w80 (wz Bb) w96 w104 w112 w120 w128 w136)
          /\ rw_cells asegs m1 (q + 144) (arp_sg2 w144 w152 w160 (wz ee) (wz ASHB) w184 w192 w200 w208 w216 w224 w232)
          /\ rw_cells asegs m1 (q + 240) (arp_sg3 x240 x248 x256 x264 x272 x280 x288 x296 x304 x312 x320' x328' x336')
          /\ rw_cells asegs m1 ee (entry_cells (upd_version E v) pad1 pad2 pad3 pad4) /\ (v = en_version E \/ 0 <= v < 2^16) /\
         (  (exists line : Z, (line = 367 \/ line = 374) /\ w48' = w48 /\ x320' = x320 /\ x328' = x328 /\ x336' = x336 /\
             ms' = MS (mkR rax (Z_to_bv 64 q) gp tp t0 t1 t2 s0w (Z_to_bv 64 q) a0' a1' a2' a3' a4' a5' a6 a7
                           (Z_to_bv 64 2) s3 (Z_to_bv 64 line) s5 s6 s7' (Z_to_bv 64 cur) s9 s10' s11 t3 t4 t5 t6)
                      F (Z_to_bv 64 ADE_TA) fc None m1 (seg_rom asegs))
         \/ (exists elen : Z, 0 <= elen /\ 4 + elen <= rem /\ 0 <= v < 2^16 /\
             x320' = wz (cur + 4) /\ x328' = wz Bb /\ x336' = wz elen /\ s7' = wz (rem - 4) /\ s10' = wz elen /\
             (  (v <> AECH_VERSION /\ w48' = w48 /\
                 ms' = MS (mkR rax (Z_to_bv 64 q) gp tp t0 t1 t2 s0w (Z_to_bv 64 q) a0' a1' a2' a3' a4' a5' a6 a7
                               (Z_to_bv 64 2) s3 (Z_to_bv 64 (cur + 4 + elen)) s5 s6 s7' (Z_to_bv 64 cur) s9 s10' s11 t3 t4 t5 t6)
                          F (Z_to_bv 64 ADE_SKIP) fc None m1 (seg_rom asegs))
             \/ (v = AECH_VERSION /\ w48' = wz (cur + 4 + elen) /\ a0' = wz (cur + 4) /\
                 ms' = MS (mkR rax (Z_to_bv 64 q) gp tp t0 t1 t2 s0w (Z_to_bv 64 q) a0' a1' a2' a3' a4' a5' a6 a7
                               (Z_to_bv 64 2) s3 (Z_to_bv 64 (cur + 4 + elen)) s5 s6 s7' (Z_to_bv 64 cur) s9 s10' s11 t3 t4 t5 t6)
                          F (Z_to_bv 64 ADE_J1) fc None m1 (seg_rom asegs))))))
        (MS (mkR rax (Z_to_bv 64 q) gp tp t0 t1 t2 s0w (Z_to_bv 64 q) (Z_to_bv 64 ee) a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 2) s3 s4 s5 s6 (Z_to_bv 64 rem) (Z_to_bv 64 cur) s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 ADE_R1)) fc None m (seg_rom asegs)).
  Proof.
    intros until x336. intros FA FB FC BS BC R1 CR BP BH ACCB BL EC EEP EA16 EEH EBA ACCE NSE CQ QH MI.
    unfold ADE_R1, ADE_TA, ADE_SKIP, ADE_J1 in *. unfold arp_sg1, arp_sg2, arp_sg3, AECH_VERSION, ASHB, wz in FA, FB, FC |- *.
    unfold entry_cells in EC |- *. unfold ENTRY_SIZE in EEH, EBA, ACCE, NSE. unfold ALOWSH_LO, AHI_LO in NSE. retpc. pose proof aceil_range as ACR.
    acb. pose proof (bytes_at_bound _ _ _ _ BS) as BB. unfold zlength in *.
    pose proof ACCB as (_ & AHIB & _). pose proof ACCE as (_ & AHIE & _). unfold AAPP_HI in AHIB, AHIE.
    assert (EA8 : ee mod 8 = 0) by (clear - EA16; Z.div_mod_to_equations; lia).
    pose proof (munch_refl [(q + 48, q + 56); (q + 168, q + 176); (q + 320, q + 344); (ee, ee + 2)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof ACCB as ACCB0. change (accessible m Bb blen) with (id (accessible m Bb blen)) in ACCB0.
    pose proof ACCE as ACCE0. change (accessible m ee 104) with (id (accessible m ee 104)) in ACCE0.
    (* [comment removed for export] *)
    st1. step. br. step. if_cases K0; zify_cond K0.
    { (* [comment removed for export] *)
      assert (R1' : rem = 1) by (revert K0; rewrite ?unsigned_lit by lia; lia). clear K0.
      step. step.
      apply evt_done. do 8 eexists. eexists. exists w48, x320, x328, x336, (en_version E).
      repeat match goal with |- _ /\ _ => split end; try eassumption; try (rewrite upd_version_id; eassumption).
      - left. reflexivity.
      - left. exists 367. repeat match goal with |- _ /\ _ => split end; try reflexivity. left; reflexivity. }
    assert (R2 : 2 <= rem) by (revert K0; rewrite ?unsigned_lit by lia; lia). clear K0.
    destruct (nth_error bs (Z.to_nat (cur - Bb + 0))) as [c0|] eqn:N0; [| apply nth_error_None in N0; lia].
    destruct (nth_error bs (Z.to_nat (cur - Bb + 1))) as [c1|] eqn:N1; [| apply nth_error_None in N1; lia].
    pose proof (ade_byte _ _ _ _ _ _ BS N0 ltac:(lia) ltac:(lia)) as RD0. pose proof (ade_byte _ _ _ _ _ _ BS N1 ltac:(lia) ltac:(lia)) as RD1.
    pose proof (abyte_range c0) as C0R. pose proof (abyte_range c1) as C1R.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (ACCB1 : accessible mx Bb blen) by (unfold id in ACCB0; eapply accessible_across; [exact ACCB0| exact MU|];
        repeat (apply Forall_cons; [cbn; unfold AHI_LO, ALOWSH_LO in *; lia|]); apply Forall_nil);
      assert (ACCE1 : accessible mx ee 104) by (unfold id in ACCE0; eapply accessible_across; [exact ACCE0| exact MU|];
        repeat (apply Forall_cons; [cbn; unfold AHI_LO, ALOWSH_LO in *; lia|]); apply Forall_nil) end.
    (* [comment removed for export] *)
    go.
    ck1_load ACCB1 cur v1 V1 V2 Hc1. st1.
    ck_K 12 0x553978 K1.
    { intros tv1. red_tset.
      (* [comment removed for export] *)
      go.
      ck1_load ACCB1 (cur + 1) v2 W1 W2 Hc2. step. change (zxb c0) with (Z_to_bv 64 (bv_unsigned c0)).
      ck_K 13 0x55398c K2.
      { intros tv2. red_tset.
        (* [comment removed for export] *)
        go.
        ck8_load ACCE1 ee. step. change (zxb c1) with (Z_to_bv 64 (bv_unsigned c1)). step. if_false_by (ck1_bnez_false 0 eq_refl).
        (* [comment removed for export] *)
        step. step. step.
        rewrite Z.shiftl_mul_pow2 by lia. rewrite (unsigned_lit (bv_unsigned c0)) by lia. rewrite (unsigned_lit (bv_unsigned c0 * 2 ^ 8)) by lia. rewrite (unsigned_lit (bv_unsigned c1)) by lia.
        rewrite (be16_lor (bv_unsigned c0) (bv_unsigned c1)) by lia.
        set (v := bv_unsigned c1 + 256 * bv_unsigned c0) in *. assert (VR : 0 <= v < 2^16) by (subst v; lia).
        clear ACCB1 ACCE1. st1.
        (* [comment removed for export] *)
        step. step. if_cases K0; zify_cond K0.
        { (* [comment removed for export] *)
          apply evt_done. do 8 eexists. eexists. exists w48, x320, x328, x336, v.
          repeat match goal with |- _ /\ _ => split end; try eassumption.
          - right. exact VR.
          - left. exists 374. repeat match goal with |- _ /\ _ => split end; try reflexivity. right; reflexivity. }
        assert (R4 : 4 <= rem) by (revert K0; rewrite ?unsigned_lit by lia; rewrite land_even_mask, land_W64, land_1, Z.mod_small by lia; clear - R2; intros K0; lia). clear K0.
        destruct (nth_error bs (Z.to_nat (cur - Bb + 2))) as [c2|] eqn:N2; [| apply nth_error_None in N2; lia].
        destruct (nth_error bs (Z.to_nat (cur - Bb + 3))) as [c3|] eqn:N3; [| apply nth_error_None in N3; lia].
        pose proof (abyte_range c2) as C2R. pose proof (abyte_range c3) as C3R.
        lazymatch goal with BSx : bytes_at asegs ?mx Bb bs |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
          pose proof (ade_byte _ _ _ _ _ _ BSx N2 ltac:(lia) ltac:(lia)) as RD2; pose proof (ade_byte _ _ _ _ _ _ BSx N3 ltac:(lia) ltac:(lia)) as RD3 end.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
          assert (ACCB2 : accessible mx Bb blen) by (unfold id in ACCB0; eapply accessible_across; [exact ACCB0| exact MU|];
            repeat (apply Forall_cons; [cbn; unfold AHI_LO, ALOWSH_LO in *; lia|]); apply Forall_nil) end.
        (* [comment removed for export] *)
        go.
        ck1_load ACCB2 (cur + 2) v4 X1 X2 Hc4.
        ck_K 13 0x5539ec K3.
        { intros tv3. red_tset.
          (* [comment removed for export] *)
          go.
          ck1_load ACCB2 (cur + 3) v5 Y1 Y2 Hc5. step. change (zxb c2) with (Z_to_bv 64 (bv_unsigned c2)).
          ck_K 14 0x553a04 K4.
          { intros tv4. red_tset.
            (* [comment removed for export] *)
            clear ACCB2. step. change (zxb c3) with (Z_to_bv 64 (bv_unsigned c3)). step. step.
            rewrite Z.shiftl_mul_pow2 by lia. rewrite (unsigned_lit (bv_unsigned c2)) by lia. rewrite (unsigned_lit (bv_unsigned c2 * 2 ^ 8)) by lia. rewrite (unsigned_lit (bv_unsigned c3)) by lia.
            rewrite (be16_lor (bv_unsigned c2) (bv_unsigned c3)) by lia.
            set (elen := bv_unsigned c3 + 256 * bv_unsigned c2) in *. assert (ELR : 0 <= elen < 2^16) by (subst elen; lia).
            (* [comment removed for export] *)
            step. step. if_cases K0; zify_cond K0.
            { (* [comment removed for export] *)
              assert (RL : rem - 4 < elen) by (revert K0; rewrite ?unsigned_lit by lia; clear - R4 ELR; intros K0; lia). clear K0.
              apply evt_done. do 8 eexists. eexists. exists w48, x320, x328, x336, v.
              repeat match goal with |- _ /\ _ => split end; try eassumption.
              - right. exact VR.
              - left. exists 374. repeat match goal with |- _ /\ _ => split end; try reflexivity. right; reflexivity. }
            assert (RL : elen <= rem - 4) by (revert K0; rewrite ?unsigned_lit by lia; clear - R4 ELR; intros K0; lia). clear K0.
            (* [comment removed for export] *)
            step. step. step. rewrite ?unsigned_lit by lia. rewrite zb_lxor_ones by lia. ub_dead.
            go.
            if_cases K0; zify_cond K0.
            { (* [comment removed for export] *)
              assert (NV : v <> AECH_VERSION) by (unfold AECH_VERSION; revert K0; rewrite ?unsigned_lit by lia; clear - VR; intros K0; lia). unfold AECH_VERSION in NV.
              apply evt_done. do 8 eexists. eexists. exists w48. do 3 eexists. exists v.
              repeat match goal with |- _ /\ _ => split end; try eassumption.
              - right. exact VR.
              - right. exists elen.
                do 8 (split; [first [lia | exact VR | reflexivity]|]).
                left. split; [exact NV|]. split; reflexivity. }
            assert (EV : v = AECH_VERSION) by (unfold AECH_VERSION; revert K0; rewrite ?unsigned_lit by lia; clear - VR; intros K0; lia). unfold AECH_VERSION in EV. clear K0.
            st1.
            apply evt_done. do 8 eexists. eexists. eexists. do 3 eexists. exists v.
            repeat match goal with |- _ /\ _ => split end; try eassumption.
            - right. exact VR.
            - right. exists elen.
              do 8 (split; [first [lia | exact VR | reflexivity]|]).
              right. split; [exact EV|]. split; [reflexivity|]. split; reflexivity. }
          ck1_branch_blt (cur + 3) v5 Y1 Y2 Hc5 K4. }
        ck1_branch_blt (cur + 2) v4 X1 X2 Hc4 K3. }
      ck1_branch_blt (cur + 1) v2 W1 W2 Hc2 K2. }
    ck1_branch_blt cur v1 V1 V2 Hc1 K1.
  Qed.

  (* [comment removed for export] *)
  Lemma ade_seg3 :
    forall (rax gp tp t0 t1 t2 s0w a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s9 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (q cur elen Bb blen ee : Z) (bs : list byte) (E : entrep) pad1 pad2 pad3 pad4
           (w16 w24 w32 w40 w48 w56 w64 w72 w80 w96 w104 w112 w120 w128 w136 : word)
           (w144 w152 w160 w184 w192 w200 w208 w216 w224 w232 : word)
           (x240 x248 x256 x264 x272 x280 x288 x296 x304 x312 x320 x328 x336 : word),
      rw_cells asegs m (q + 16) (arp_sg1 w16 w24 w32 w40 w48 w56 w64 w72 w80 (wz Bb) w96 w104 w112 w120 w128 w136) ->
      rw_cells asegs m (q + 144) (arp_sg2 w144 w152 w160 (wz ee) (wz ASHB) w184 w192 w200 w208 w216 w224 w232) ->
      rw_cells asegs m (q + 240) (arp_sg3 x240 x248 x256 x264 x272 x280 x288 x296 x304 x312 x320 x328 x336) ->
      bytes_at asegs m Bb bs -> Bb <= cur -> 0 <= elen -> cur + 4 + elen <= Bb + zlength bs -> 0 < Bb -> Bb + zlength bs <= aceil ->
      accessible m Bb blen -> zlength bs <= blen ->
      rw_cells asegs m ee (entry_cells E pad1 pad2 pad3 pad4) -> length pad3 = 6%nat -> 0 < ee -> ee + ENTRY_SIZE <= aceil -> (Bb + zlength bs <= ee \/ ee + ENTRY_SIZE <= Bb) ->
      accessible m ee ENTRY_SIZE -> (ee + ENTRY_SIZE <= ALOWSH_LO \/ AHI_LO <= ee) ->
      aceil <= q -> q + 344 < 2^64 -> mem_inv asegs m ->
      evt asegs (fun ms' => exists (a0' a1' a2' a3' a4' s5' s6' : word) m1 (w32' w40' x296' x304' x312' x320' x336' : word) (cf : Z),
          munch [(q + 32, q + 48); (q + 296, q + 328); (q + 336, q + 344); (ee + 49, ee + 50)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
          /\ rw_cells asegs m1 (q + 16) (arp_sg1 w16 w24 w32' w40' w48 w56 w64 w72 w80 (wz Bb) w96 w104 w112 w120 w128 w136)
          /\ rw_cells asegs m1 (q + 240) (arp_sg3 x240 x248 x256 x264 x272 x280 x288 x296' x304' x312' x320' x328 x336')
          /\ rw_cells asegs m1 ee (entry_cells (upd_cfgid E cf) pad1 pad2 pad3 pad4) /\ (cf = en_cfgid E \/ 0 <= cf < 256) /\
         (  ms' = MS (mkR rax (Z_to_bv 64 q) gp tp t0 t1 t2 s0w (Z_to_bv 64 q) a0' a1' a2' a3' a4' a5 a6 a7
                        s2 s3 (Z_to_bv 64 400) s5' s6' s7 (Z_to_bv 64 cur) s9 (Z_to_bv 64 elen) s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 ADE_TA) fc None m1 (seg_rom asegs)
         \/ (exists publen, publen = 256 * bz bs (Z.to_nat (cur - Bb + 7)) + bz bs (Z.to_nat (cur - Bb + 8)) /\ 5 + publen <= elen /\
             cf = bz bs (Z.to_nat (cur - Bb + 4)) /\ w32' = wz (ee + 24) /\ w40' = wz (ee + 16) /\
             x296' = wz (cur + 9) /\ x304' = wz Bb /\ x312' = wz publen /\ x320' = wz (cur + 9 + publen) /\ x336' = wz (elen - 5 - publen) /\
             ms' = MS (mkR (Z_to_bv 64 ADE_R2) (Z_to_bv 64 q) gp tp t0 t1 t2 s0w (Z_to_bv 64 q)
                           (Z_to_bv 64 (q + 296)) (Z_to_bv 64 (ee + 24)) (Z_to_bv 64 (ee + 16)) (Z_to_bv 64 (cur + 9 + publen)) (Z_to_bv 64 cur) a5 a6 a7
                           s2 s3 (Z_to_bv 64 400) (Z_to_bv 64 (bz bs (Z.to_nat (cur - Bb + 5)))) (Z_to_bv 64 (bz bs (Z.to_nat (cur - Bb + 6)))) s7 (Z_to_bv 64 cur) s9 (Z_to_bv 64 elen) s11 t3 t4 t5 t6)
                      F (Z_to_bv 64 P_PACKET_memdup) fc None m1 (seg_rom asegs))))
        (MS (mkR rax (Z_to_bv 64 q) gp tp t0 t1 t2 s0w (Z_to_bv 64 q) (Z_to_bv 64 (cur + 4)) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 (Z_to_bv 64 cur) s9 (Z_to_bv 64 elen) s11 t3 t4 t5 t6)
            F (Z_to_bv 64 ADE_J1) fc None m (seg_rom asegs)).
  Proof.
    intros until x336. intros FA FB FC BS BC EL0 CR BP BH ACCB BL EC L3 EEP EEH EBA ACCE NSE CQ QH MI.
    unfold ADE_J1, ADE_TA, ADE_R2, P_PACKET_memdup in *. unfold arp_sg1, arp_sg2, arp_sg3, ASHB, wz in FA, FB, FC |- *.
    unfold entry_cells in EC |- *. unfold ENTRY_SIZE in EEH, EBA, ACCE, NSE. unfold ALOWSH_LO, AHI_LO in NSE. pose proof aceil_range as ACR.
    acb. pose proof (bytes_at_bound _ _ _ _ BS) as BB. unfold zlength in *.
    pose proof ACCB as (_ & AHIB & _). pose proof ACCE as (_ & AHIE & _). unfold AAPP_HI in AHIB, AHIE.
    pose proof (munch_refl [(q + 32, q + 48); (q + 296, q + 328); (q + 336, q + 344); (ee + 49, ee + 50)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof ACCB as ACCB0. change (accessible m Bb blen) with (id (accessible m Bb blen)) in ACCB0.
    pose proof ACCE as ACCE0. change (accessible m ee 104) with (id (accessible m ee 104)) in ACCE0.
    Local Ltac reaccB ACCB0 MU N := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (N : accessible mx _ _) by (unfold id in ACCB0; eapply accessible_across; [exact ACCB0| exact MU|];
        repeat (apply Forall_cons; [cbn; unfold AHI_LO, ALOWSH_LO in *; lia|]); apply Forall_nil) end.
    Local Ltac exitTA0 := apply evt_done; do 7 eexists; eexists; do 7 eexists; eexists;
      repeat match goal with |- _ /\ _ => split end; [eassumption| eassumption| eassumption| eassumption| eassumption| | | left; reflexivity];
      [| left; reflexivity]; rewrite upd_cfgid_id; eassumption.
    Local Ltac exitTA1 := apply evt_done; do 7 eexists; eexists; do 7 eexists; eexists;
      repeat match goal with |- _ /\ _ => split end; [eassumption| eassumption| eassumption| eassumption| eassumption| | | left; reflexivity];
      [lazymatch goal with H : rw_cells _ ?mx ?eex (C2 _ :: _) |- rw_cells _ _ ?eex _ => rewrite Z.mod_small in H by lia; exact H end|]; right; lia.
    (* [comment removed for export] *)
    go. if_cases K0; zify_cond K0.
    { (* [comment removed for export] *)
      go_to ADE_TA. exitTA0. }
    assert (EL1 : 1 <= elen) by (revert K0; rewrite ?unsigned_lit by lia; lia). clear K0.
    destruct (nth_error bs (Z.to_nat (cur - Bb + 4))) as [c4|] eqn:N4; [| apply nth_error_None in N4; lia]. pose proof (abyte_range c4) as C4R.
    pose proof (ade_byte _ _ _ _ _ _ BS N4 ltac:(lia) ltac:(lia)) as RD4.
    (* [comment removed for export] *)
    go. ck1_load ACCB (cur + 4) v6 V1 V2 Hc6.
    ck_K 12 0x553a60 K1.
    { intros tv1. red_tset.
      (* [comment removed for export] *)
      go. ck1_load ACCE (ee + 49) v7 W1 W2 Hc7. step. change (zxb c4) with (Z_to_bv 64 (bv_unsigned c4)).
      ck_K 14 0x553a7c K2.
      { intros tv2. red_tset.
        (* [comment removed for export] *)
        clear ACCB ACCE. go.
        (* [comment removed for export] *)
        if_cases K0; zify_cond K0.
        { (* [comment removed for export] *)
          go_to ADE_TA. exitTA1. }
        assert (EL3 : 3 <= elen) by (revert K0; rewrite ?unsigned_lit by lia; lia). clear K0.
        destruct (nth_error bs (Z.to_nat (cur - Bb + 5))) as [c5|] eqn:N5; [| apply nth_error_None in N5; lia]. pose proof (abyte_range c5) as C5R.
        destruct (nth_error bs (Z.to_nat (cur - Bb + 6))) as [c6|] eqn:N6; [| apply nth_error_None in N6; lia]. pose proof (abyte_range c6) as C6R.
        lazymatch goal with BSx : bytes_at asegs ?mx Bb bs |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
          pose proof (ade_byte _ _ _ _ _ _ BSx N5 ltac:(lia) ltac:(lia)) as RD5; pose proof (ade_byte _ _ _ _ _ _ BSx N6 ltac:(lia) ltac:(lia)) as RD6 end.
        reaccB ACCB0 MU ACCB2.
        (* [comment removed for export] *)
        go. ck1_load ACCB2 (cur + 5) v8 X1 X2 Hc8.
        ck_K 12 0x553ac0 K3.
        { intros tv3. red_tset.
          (* [comment removed for export] *)
          go. ck1_load ACCB2 (cur + 6) v9 Y1 Y2 Hc9. step.
          ck_K 13 0x553ad8 K4.
          { intros tv4. red_tset.
            (* [comment removed for export] *)
            clear ACCB2. go. if_cases K0; zify_cond K0.
            { (* [comment removed for export] *)
              go_to ADE_TA. exitTA1. }
            assert (EL5 : 5 <= elen) by (revert K0; rewrite ?unsigned_lit by lia; lia). clear K0.
            destruct (nth_error bs (Z.to_nat (cur - Bb + 7))) as [c7|] eqn:N7; [| apply nth_error_None in N7; lia]. pose proof (abyte_range c7) as C7R.
            destruct (nth_error bs (Z.to_nat (cur - Bb + 8))) as [c8|] eqn:N8; [| apply nth_error_None in N8; lia]. pose proof (abyte_range c8) as C8R.
            lazymatch goal with BSx : bytes_at asegs ?mx Bb bs |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
              pose proof (ade_byte _ _ _ _ _ _ BSx N7 ltac:(lia) ltac:(lia)) as RD7; pose proof (ade_byte _ _ _ _ _ _ BSx N8 ltac:(lia) ltac:(lia)) as RD8 end.
            reaccB ACCB0 MU ACCB3.
            (* [comment removed for export] *)
            go. ck1_load ACCB3 (cur + 7) v10 Z1 Z2 Hc10.
            ck_K 12 0x553b20 K5.
            { intros tv5. red_tset.
              (* [comment removed for export] *)
              go. ck1_load ACCB3 (cur + 8) v11 U1 U2 Hc11. step.
              ck_K 13 0x553b3c K6.
              { intros tv6. red_tset.
                (* [comment removed for export] *)
                clear ACCB3. go.
                change (zxb c7) with (Z_to_bv 64 (bv_unsigned c7)). change (zxb c8) with (Z_to_bv 64 (bv_unsigned c8)).
                rewrite (unsigned_lit (bv_unsigned c7)) by lia. rewrite Z.shiftl_mul_pow2 by lia. rewrite (unsigned_lit (bv_unsigned c7 * 2 ^ 8)) by lia. rewrite (unsigned_lit (bv_unsigned c8)) by lia.
                rewrite (be16_lor (bv_unsigned c7) (bv_unsigned c8)) by lia.
                set (publen := bv_unsigned c8 + 256 * bv_unsigned c7) in *. assert (PLR : 0 <= publen < 2^16) by (subst publen; lia).
                if_cases K0; zify_cond K0.
                { (* [comment removed for export] *)
                  go_to ADE_TA. exitTA1. }
                assert (PL : 5 + publen <= elen) by (revert K0; rewrite ?unsigned_lit by lia; lia). clear K0.
                (* [comment removed for export] *)
                go. rewrite zb_lxor_ones by lia. ub_dead. go. step.
                apply evt_done. do 7 eexists. eexists. do 7 eexists. eexists.
                repeat match goal with |- _ /\ _ => split end; try eassumption;
                  [lazymatch goal with H : rw_cells _ ?mx ?eex (C2 _ :: _) |- rw_cells _ _ ?eex _ => rewrite Z.mod_small in H by lia; exact H end| right; lia|].
                right. exists publen. unfold bz. rewrite N4, N5, N6, N7, N8.
                repeat match goal with |- _ /\ _ => split end; try reflexivity; try lia; try (f_equal; lia). }
              ck1_branch_blt (cur + 8) v11 U1 U2 Hc11 K6. }
            ck1_branch_blt (cur + 7) v10 Z1 Z2 Hc10 K5. }
          ck1_branch_blt (cur + 6) v9 Y1 Y2 Hc9 K4. }
        ck1_branch_blt (cur + 5) v8 X1 X2 Hc8 K3. }
      ck1_branch_blt (ee + 49) v7 W1 W2 Hc7 K2. }
    ck1_branch_blt (cur + 4) v6 V1 V2 Hc6 K1.
    Unshelve. all: try exact (Z_to_bv 64 0); try exact 0.
  Qed.

  (* [comment removed for export] *)
  Lemma ade_seg4 :
    forall (rax gp tp t0 t1 t2 s0w a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (q : Z),
      aceil <= q -> q + 344 < 2^64 ->
      evt asegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 ADE_R2a) (Z_to_bv 64 q) gp tp t0 t1 t2 s0w (Z_to_bv 64 q) (Z_to_bv 64 (q + 320)) (Z_to_bv 64 (q + 272)) a2 a3 a4 a5 a6 a7
                                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 BK_get2) fc None m (seg_rom asegs))
        (MS (mkR rax (Z_to_bv 64 q) gp tp t0 t1 t2 s0w (Z_to_bv 64 q) (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 ADE_R2)) fc None m (seg_rom asegs)).
  Proof.
    (* [comment removed for export] *)
    intros until q. intros CQ QH.
    (* [comment removed for export] *)
    unfold ADE_R2, ADE_R2a, BK_get2 in *. retpc. pose proof aceil_range as ACR.
    (* [comment removed for export] *)
    go. step.
    (* [comment removed for export] *)
    apply evt_done. reflexivity.
  Qed.

  Lemma land1K : forall x, Z.land x 1 = x mod 2.
  Proof.
    intros x. change 1 with (Z.ones 1). rewrite Z.land_ones by lia. reflexivity.
  Qed.

  Lemma ade_seg4b :
    forall (rax gp tp t0 t1 t2 s0w a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (q rv c2 ms2 so ee : Z) (E : entrep) pad1 pad2 pad3 pad4,
      (rv = 0 \/ (rv = 1 /\ 0 <= so < 2^16 /\ rw_cells asegs m (q + 272) (pk_cells c2 ms2 so))) ->
      rw_cells asegs m (q + 168) [C8 (wz ee); C8 (wz ASHB)] ->
      rw_cells asegs m ee (entry_cells E pad1 pad2 pad3 pad4) -> 0 < ee -> ee mod 16 = 0 -> ee + ENTRY_SIZE <= aceil -> accessible m ee ENTRY_SIZE ->
      aceil <= q -> q + 344 < 2^64 -> mem_inv asegs m ->
      evt asegs (fun ms' => exists (a0' a1' a2' : word) m1 ns,
          munch [(ee + 32, ee + 36)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
          /\ rw_cells asegs m1 ee (entry_cells (upd_nsuites E ns) pad1 pad2 pad3 pad4) /\
         (  (ns = en_nsuites E /\
             ms' = MS (mkR rax (Z_to_bv 64 q) gp tp t0 t1 t2 s0w (Z_to_bv 64 q) a0' a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                      F (Z_to_bv 64 ADE_TA) fc None m1 (seg_rom asegs))
         \/ (rv = 1 /\ 2 <= so /\ so mod 2 = 0 /\ ns = so / 4 /\
             ms' = MS (mkR (Z_to_bv 64 ADE_R3) (Z_to_bv 64 q) gp tp t0 t1 t2 s0w (Z_to_bv 64 q) (Z_to_bv 64 ns) (Z_to_bv 64 6) (Z_to_bv 64 ADE_FILE) (Z_to_bv 64 405) a4 a5 a6 a7
                           (Z_to_bv 64 ASHB) s3 (Z_to_bv 64 (Z.shiftr (ee + 32) 3 + ASHB)) s5 s6 s7 s8 (Z_to_bv 64 ee) s10 (Z_to_bv 64 (ee + 32)) t3 t4 t5 t6)
                      F (Z_to_bv 64 P_CRYPTO_malloc_array) fc None m1 (seg_rom asegs))))
        (MS (mkR rax (Z_to_bv 64 q) gp tp t0 t1 t2 s0w (Z_to_bv 64 q) (Z_to_bv 64 rv) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 ADE_R2a)) fc None m (seg_rom asegs)).
  Proof.
    (* [comment removed for export] *)
    intros until pad4. intros RV FE EC EEP EEA EEH ACCE CQ QH MI.
    assert (RVR : 0 <= rv <= 1) by (destruct RV as [->|(-> & _)]; lia).
    unfold ADE_R2a, ADE_TA, ADE_R3, ADE_FILE, P_CRYPTO_malloc_array in *. unfold pk_cells, ASHB, wz in FE |- *.
    unfold entry_cells in EC |- *. unfold ENTRY_SIZE in EEH, ACCE. pose proof aceil_range as ACR. retpc.
    acb. pose proof ACCE as (_ & AHIE & _). unfold AAPP_HI in AHIE.
    pose proof (munch_refl [(ee + 32, ee + 36)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    Local Ltac exit4b := apply evt_done; do 3 eexists; eexists; eexists;
      (* [comment removed for export] *)
      repeat match goal with |- _ /\ _ => split end; [eassumption| eassumption| eassumption| | left; split; [reflexivity| reflexivity]];
      rewrite upd_nsuites_id; eassumption.
    go.
    if_cases K0; zify_cond K0.
    { exit4b. }
    destruct RV as [R0|(R1 & SOR & FQ)]; [exfalso; subst rv; revert K0; rewrite ?unsigned_lit by lia; intros K0; lia|]. clear K0.
    unfold pk_cells, wz in FQ.
    (* [comment removed for export] *)
    go.
    if_cases K0; zify_cond K0.
    { exit4b. }
    assert (S1 : 1 <= so) by (revert K0; rewrite ?land_ones64; intros K0; Z.div_mod_to_equations; lia). clear K0.
    go.
    if_cases K0; zify_cond K0.
    (* [comment removed for export] *)
    { exit4b. }
    assert (EV : so mod 2 = 0) by (revert K0; rewrite ?unsigned_lit by lia; rewrite land1K; intros K0; lia). clear K0.
    go.
    ck4_load ACCE (ee + 32) v1 V1 V2 Ha1.
    ck_K 12 0x553be8 K1.
    { intros tv1. red_tset. go. step.
      (* [comment removed for export] *)
      rewrite ?(Z.shiftr_div_pow2 so 2) in * by lia. change (2 ^ 2) with 4 in *.
      apply evt_done. do 3 eexists. eexists. exists (so / 4).
      repeat match goal with |- _ /\ _ => split end; try eassumption.
      right. repeat match goal with |- _ /\ _ => split end; try reflexivity; try lia. }
    ck4_branch_blt (ee + 32) v1 V1 V2 Ha1 K1.
    Unshelve. all: try exact (Z_to_bv 64 0); try exact 0.
  Qed.

  (* [comment removed for export] *)
  Lemma ade_seg5 :
    forall (rax gp tp t0 t1 t2 s0w a1 a2 a3 a4 a5 a6 a7 s3 s4 s7 s8 s10 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (q kh5 kl6 c2 ms2 so ee SA : Z) (E : entrep) pad1 pad2 pad3 pad4,
      0 <= kh5 < 256 -> 0 <= kl6 < 256 -> 0 <= SA < 2^64 -> SA mod 16 = 0 ->
      rw_cells asegs m (q + 272) (pk_cells c2 ms2 so) -> 0 <= c2 < 2^64 -> 0 <= so < 2^64 ->
      rw_cells asegs m ee (entry_cells E pad1 pad2 pad3 pad4) -> 0 < ee -> ee mod 16 = 0 -> ee + ENTRY_SIZE <= aceil -> accessible m ee ENTRY_SIZE ->
      aceil <= q -> q + 344 < 2^64 -> mem_inv asegs m ->
      evt asegs (fun ms' => exists (a2' : word) m1,
          munch [(ee + 40, ee + 48)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
          /\ rw_cells asegs m1 ee (entry_cells (upd_suites E SA (en_suites_o E)) pad1 pad2 pad3 pad4) /\
         (  (SA = 0 /\
             ms' = MS (mkR rax (Z_to_bv 64 q) gp tp t0 t1 t2 s0w (Z_to_bv 64 q) (Z_to_bv 64 0) (Z_to_bv 64 (ee + 40)) a2' a3 a4 a5 a6 a7
                           (Z_to_bv 64 ASHB) s3 s4 (Z_to_bv 64 kh5) (Z_to_bv 64 kl6) s7 s8 (Z_to_bv 64 (0 - 4)) s10 (Z_to_bv 64 (ee + 32)) t3 t4 t5 t6)
                      F (Z_to_bv 64 ADE_TZ) fc None m1 (seg_rom asegs))
         \/ (0 < SA /\
             ms' = MS (mkR rax (Z_to_bv 64 q) gp tp (Z_to_bv 64 (0 - 1)) (Z_to_bv 64 c2) t2 s0w (Z_to_bv 64 q)
                           (Z_to_bv 64 SA) (Z_to_bv 64 (ee + 40)) (Z_to_bv 64 c2) a3 (Z_to_bv 64 0) (Z_to_bv 64 so) (Z_to_bv 64 (256 * kh5 + kl6)) (Z_to_bv 64 0)
                           (Z_to_bv 64 ASHB) s3 s4 (Z_to_bv 64 (256 * kh5)) (Z_to_bv 64 4) s7 s8 (Z_to_bv 64 (0 - 4)) s10 (Z_to_bv 64 (ee + 32)) t3 t4 t5 t6)
                      F (Z_to_bv 64 ADE_LH) fc None m1 (seg_rom asegs))))
        (MS (mkR rax (Z_to_bv 64 q) gp tp t0 t1 t2 s0w (Z_to_bv 64 q) (Z_to_bv 64 SA) a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 ASHB) s3 s4 (Z_to_bv 64 kh5) (Z_to_bv 64 kl6) s7 s8 (Z_to_bv 64 ee) s10 (Z_to_bv 64 (ee + 32)) t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 ADE_R3)) fc None m (seg_rom asegs)).
  Proof.
    (* [comment removed for export] *)
    intros until pad4. intros K5R K6R SAR SAA FQ C2R SOR EC EEP EEA EEH ACCE CQ QH MI.
    unfold ADE_R3, ADE_TZ, ADE_LH in *. unfold pk_cells, ASHB, wz in FQ |- *.
    unfold entry_cells in EC |- *. unfold ENTRY_SIZE in EEH, ACCE. pose proof aceil_range as ACR. retpc.
    acb. pose proof ACCE as (_ & AHIE & _). unfold AAPP_HI in AHIE.
    pose proof (munch_refl [(ee + 40, ee + 48)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    go.
    (* [comment removed for export] *)
    ck8_check ACCE (ee + 40).
    go.
    if_cases K0; zify_cond K0.
    { assert (SZ : SA = 0) by (revert K0; rewrite ?unsigned_lit by lia; intros K0; lia). clear K0. subst SA.
      go_to ADE_TZ.
      apply evt_done. eexists. eexists.
      (* [comment removed for export] *)
      repeat match goal with |- _ /\ _ => split end; try eassumption. left. split; [reflexivity| reflexivity]. }
    assert (SP : 0 < SA) by (revert K0; rewrite ?unsigned_lit by lia; intros K0; lia). clear K0.
    go_to ADE_LH.
    rewrite Z.shiftl_mul_pow2 by lia. rewrite (unsigned_lit (kh5 * 2 ^ 8)) by lia. rewrite (unsigned_lit kl6) by lia. rewrite (be16_lor kh5 kl6) by lia.
    rewrite (unsigned_lit SA) by lia. rewrite land1K. replace (SA mod 2) with 0 by lia. replace (kh5 * 2 ^ 8) with (256 * kh5) by lia. replace (kl6 + 256 * kh5) with (256 * kh5 + kl6) by lia.
    apply evt_done. eexists. eexists.
    repeat match goal with |- _ /\ _ => split end; try eassumption. right. split; [lia| reflexivity].
    Unshelve. all: try exact (Z_to_bv 64 0); try exact 0.
  Qed.

  Lemma rw_cells_recutK : forall m A cs cs',
    rw_cells asegs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> rw_cells asegs m A cs'.
  Proof.
    intros m A cs cs' [[WF B] W] WF' E. split; [split; [exact WF'| rewrite E; exact B]|].
    rewrite <- (cells_bytes_length cs' WF'), E, (cells_bytes_length cs WF). exact W.
  Qed.

  Lemma mod16_loK : forall z, (z mod 65536) mod 256 = z mod 256.
  Proof.
    intros z. change 65536 with (256 * 256). rewrite Z.rem_mul_r, (Z.mul_comm 256), Z.mod_add, Z.mod_mod by lia. reflexivity.
  Qed.

  Lemma mod16_hiK : forall z, (z mod 65536) / 256 = (z / 256) mod 256.
  Proof.
    intros z. change 65536 with (256 * 256). rewrite Z.rem_mul_r by lia. rewrite (Z.mul_comm 256), Z.div_add by lia. rewrite Z.div_small by (apply Z.mod_pos_bound; lia). lia.
  Qed.

  Lemma le2_mod16K : forall z1 z2, 0 <= z1 < 2^64 -> 0 <= z2 < 2^64 -> z1 mod 65536 = z2 mod 65536 -> le2 (Z_to_bv 64 z1) = le2 (Z_to_bv 64 z2).
  Proof.
    intros z1 z2 P1 P2 E. unfold le2. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64). rewrite !(Z.mod_small _ (2^64)) by lia.
    cbn [Z_to_le_bytes]. rewrite !Z.shiftr_div_pow2 by lia. change (2^8) with 256.
    f_equal; [| f_equal]; apply bv_eq; rewrite !Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 8) with 256.
    - rewrite <- (mod16_loK z1), <- (mod16_loK z2), E. reflexivity.
    - rewrite <- (mod16_hiK z1), <- (mod16_hiK z2), E. reflexivity.
  Qed.

  Lemma lor_add_disjoint_uK : forall x y k, 0 <= k -> 0 <= x < 2^k -> 0 <= y -> Z.lor x (y * 2^k) = x + y * 2^k.
  Proof.
    intros x y k Hk Hx Hy. destruct (Z.eq_dec x 0) as [->|NZ]. { rewrite Z.lor_0_l. lia. }
    assert (D : Z.land x (y * 2^k) = 0).
    { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
      destruct (Z.lt_ge_cases i k) as [LT|GE].
      - rewrite (Z.mul_pow2_bits_low y k i) by lia. apply andb_false_r.
      - assert (LX : Z.log2 x < k) by (apply (proj1 (Z.log2_lt_pow2 x k ltac:(lia))); lia).
        rewrite (Z.bits_above_log2 x i) by lia. reflexivity. }
    rewrite <- Z.lxor_lor by exact D. symmetry. apply Z.add_nocarry_lxor. exact D.
  Qed.

  Lemma ub_byte1K : forall w, 0 <= w -> bv_unsigned (Z_to_bv 64 (Z.shiftl w 48)) / 2^56 = (w mod 65536) / 256.
  Proof.
    intros w Hw. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (65536 * 2^48). rewrite Z.shiftl_mul_pow2 by lia.
    rewrite Z.mul_mod_distr_r by lia. change (2^56) with (256 * 2^48). rewrite Z.div_mul_cancel_r by lia. reflexivity.
  Qed.

  Lemma ub_kdfK : forall b0 b1 b2 b3, 0 <= b0 < 256 -> 0 <= b1 < 256 -> 0 <= b2 < 256 -> 0 <= b3 < 256 ->
    let w := b0 + b1 * 2^8 + (b2 * 2^16 + b3 * 2^24) in
    (w * 2^8 + (w mod 65536) / 256) mod 65536 = (256 * b0 + b1) mod 65536 /\ ((w / 2^16) * 2^8 + b3) mod 65536 = (256 * b2 + b3) mod 65536
    /\ 0 <= w < 2^32 /\ (w mod 65536) / 256 = b1 /\ w / 2^16 = b2 + 256 * b3.
  Proof.
    intros b0 b1 b2 b3 H0 H1 H2 H3 w.
    assert (M : w mod 65536 = b0 + b1 * 256) by (subst w; replace (b0 + b1 * 2^8 + (b2 * 2^16 + b3 * 2^24)) with ((b0 + b1 * 256) + (b2 + 256 * b3) * 65536) by lia; rewrite Z.mod_add by lia; apply Z.mod_small; lia).
    assert (B1 : (w mod 65536) / 256 = b1) by (rewrite M; rewrite Z.div_add by lia; rewrite Z.div_small by lia; lia).
    assert (D : w / 2^16 = b2 + 256 * b3) by (subst w; replace (b0 + b1 * 2^8 + (b2 * 2^16 + b3 * 2^24)) with ((b0 + b1 * 256) + (b2 + 256 * b3) * 2^16) by lia; rewrite Z.div_add by lia; rewrite Z.div_small by lia; lia).
    rewrite B1, D. split; [| split; [| split; [subst w; lia| split; reflexivity]]].
    - subst w. replace ((b0 + b1 * 2^8 + (b2 * 2^16 + b3 * 2^24)) * 2^8 + b1) with ((256 * b0 + b1) + (b1 + b2 * 256 + b3 * 65536) * 65536) by lia. rewrite Z.mod_add by lia. reflexivity.
    - replace ((b2 + 256 * b3) * 2^8 + b3) with ((256 * b2 + b3) + b3 * 65536) by lia. rewrite Z.mod_add by lia. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma ade_loop : forall (k : nat) (i : Z) (rax gp tp t2 s0w a1 a3 s2 s3 s5 s7 s8 s10 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (q Bb blen c2 ms2 so ns kem SA ee : Z) (bs : list byte) (E : entrep) pad1 pad2 pad3 pad4 junk,
      Z.of_nat k = ns - i -> 0 <= i <= ns -> en_nsuites E = ns -> ns = so / 4 -> 0 <= so < 2^16 -> 0 <= kem < 2^16 ->
      rw_cells asegs m (q + 176) [C8 (wz ASHB)] -> rw_cells asegs m (q + 272) (pk_cells (c2 + 4 * i) ms2 (so - 4 * i)) -> 0 <= ms2 < 2^64 ->
      rw_cells asegs m (SA + 6 * i) [CB (Z.to_nat (6 * (ns - i))) junk] -> 0 < SA -> SA mod 16 = 0 -> SA + 6 * ns <= aceil -> accessible m SA (6 * ns) -> (SA + 6 * ns <= ALOWSH_LO \/ AHI_LO <= SA) ->
      bytes_at asegs m Bb bs -> 0 < Bb -> Bb <= c2 -> c2 + so <= Bb + zlength bs -> Bb + zlength bs <= aceil -> accessible m Bb blen -> zlength bs <= blen ->
      (SA + 6 * ns <= Bb \/ Bb + zlength bs <= SA) ->
      rw_cells asegs m ee (entry_cells E pad1 pad2 pad3 pad4) -> 0 < ee -> ee mod 16 = 0 -> ee + ENTRY_SIZE <= aceil -> accessible m ee ENTRY_SIZE -> (SA + 6 * ns <= ee \/ ee + ENTRY_SIZE <= SA) ->
      aceil <= q -> q + 344 < 2^64 -> mem_inv asegs m ->
      evt asegs (fun ms' => exists (a1' a3' t0' t1' t2' s5' t3' t4' t5' t6' : word) m1 junk',
          munch [(SA + 6 * i, SA + 6 * ns); (q + 272, q + 296)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
          /\ rw_cells asegs m1 (SA + 6 * i) (asuite_cells (srows bs (Z.to_nat (c2 - Bb + 4 * i)) kem k) ++ [CB 0 junk'])
          /\ rw_cells asegs m1 (q + 272) (pk_cells (c2 + 4 * ns) ms2 (so - 4 * ns))
          /\ ms' = MS (mkR rax (Z_to_bv 64 q) gp tp t0' t1' t2' s0w (Z_to_bv 64 q)
                        (Z_to_bv 64 (so - 4 * ns)) a1' (Z_to_bv 64 (c2 + 4 * ns)) a3' (Z_to_bv 64 (6 * ns)) (Z_to_bv 64 (so - 4 * ns)) (Z_to_bv 64 kem) (Z_to_bv 64 0)
                        (Z_to_bv 64 4) s3 (Z_to_bv 64 (Z.shiftr (ee + 32) 3 + ASHB)) s5' (Z_to_bv 64 4) s7 s8 (Z_to_bv 64 (0 - 4)) s10 (Z_to_bv 64 (ee + 32)) t3' t4' t5' t6')
                   F (Z_to_bv 64 ADE_J2) fc None m1 (seg_rom asegs))
        (MS (mkR rax (Z_to_bv 64 q) gp tp (Z_to_bv 64 (i - 1)) (Z_to_bv 64 (c2 + 4 * i)) t2 s0w (Z_to_bv 64 q)
                 (Z_to_bv 64 SA) a1 (Z_to_bv 64 (c2 + 4 * i)) a3 (Z_to_bv 64 (6 * i)) (Z_to_bv 64 (so - 4 * i)) (Z_to_bv 64 kem) (Z_to_bv 64 0)
                 s2 s3 (Z_to_bv 64 (Z.shiftr (ee + 32) 3 + ASHB)) s5 (Z_to_bv 64 4) s7 s8 (Z_to_bv 64 (0 - 4)) s10 (Z_to_bv 64 (ee + 32)) t3 t4 t5 t6)
            F (Z_to_bv 64 ADE_LH) fc None m (seg_rom asegs)).
  Proof.
    (* [comment removed for export] *)
    induction k as [|k IH]; intros until junk; intros HK IR NSQ NSD SOR KR F176 FQ MSR SC SAP SAA SAH ACCS NSS BS BP SRC SRE BH ACCB BL SBA EC EEP EEA EEH ACCE SEA CQ QH MI.
    - unfold ADE_LH, ADE_J2, ASHB in *. unfold pk_cells, wz in F176, FQ |- *. acb. pose proof (bytes_at_bound _ _ _ _ BS) as BB. unfold zlength in *. pose proof aceil_range as ACR.
      assert (IE : i = ns) by lia. subst i.
      pose proof (munch_refl [(SA + 6 * ns, SA + 6 * ns); (q + 272, q + 296)] m) as MU. pose proof (wmono_refl asegs m) as WM.
      step. if_cases K0; zify_cond K0. 2: { exfalso. revert K0. rewrite ?unsigned_lit by lia. intros K0. Z.div_mod_to_equations. lia. }
      clear K0. go_to ADE_J2.
      apply evt_done. do 10 eexists. exists m, junk.
      repeat match goal with |- _ /\ _ => split end; try assumption. cbn [srows asuite_cells app]. rewrite Z.sub_diag in SC. exact SC.
      reflexivity.
    (* [comment removed for export] *)
    - unfold ADE_LH, ADE_J2, ASHB in *. unfold pk_cells, wz in F176, FQ |- *. acb. pose proof (bytes_at_bound _ _ _ _ BS) as BB. unfold zlength in *.
      unfold entry_cells in EC. unfold ENTRY_SIZE in *. pose proof aceil_range as ACR. unfold ALOWSH_LO, AHI_LO in NSS.
      pose proof ACCB as (_ & AHIB & _). pose proof ACCE as (_ & AHIE & _). pose proof ACCS as (_ & AHIS & _). unfold AAPP_HI in AHIB, AHIE, AHIS.
      assert (IL : i < ns) by lia.
      assert (S4 : 4 <= so - 4 * i) by (Z.div_mod_to_equations; lia).
      pose proof (munch_refl [(SA + 6 * i, SA + 6 * ns); (q + 272, q + 296)] m) as MU. pose proof (wmono_refl asegs m) as WM.
      pose proof ACCS as ACCS0. change (accessible m SA (6 * ns)) with (id (accessible m SA (6 * ns))) in ACCS0.
      pose proof ACCE as ACCE0. change (accessible m ee 104) with (id (accessible m ee 104)) in ACCE0.
      pose proof ACCB as ACCB0. change (accessible m Bb blen) with (id (accessible m Bb blen)) in ACCB0.
      (* [comment removed for export] *)
      Local Ltac reaccS ACCX0 MU N := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
        assert (N : accessible mx _ _) by (unfold id in ACCX0; eapply accessible_across; [exact ACCX0| exact MU|];
          repeat (apply Forall_cons; [cbn; unfold AHI_LO, ALOWSH_LO in *; lia|]); apply Forall_nil) end.
      step. if_cases K0; zify_cond K0. { exfalso. revert K0. rewrite ?unsigned_lit by lia. intros K0. lia. } clear K0.
      destruct (nth_error bs (Z.to_nat (c2 - Bb + 4 * i + 0))) as [e0|] eqn:M0; [| apply nth_error_None in M0; lia].
      destruct (nth_error bs (Z.to_nat (c2 - Bb + 4 * i + 1))) as [e1|] eqn:M1; [| apply nth_error_None in M1; lia].
      destruct (nth_error bs (Z.to_nat (c2 - Bb + 4 * i + 2))) as [e2|] eqn:M2; [| apply nth_error_None in M2; lia].
      destruct (nth_error bs (Z.to_nat (c2 - Bb + 4 * i + 3))) as [e3|] eqn:M3; [| apply nth_error_None in M3; lia].
      pose proof (ade_byte m Bb bs (c2 + 4 * i) 0 e0 BS ltac:(replace (c2 + 4 * i - Bb + 0) with (c2 - Bb + 4 * i + 0) by lia; exact M0) ltac:(lia) ltac:(lia)) as RD0.
      (* [comment removed for export] *)
      pose proof (ade_byte m Bb bs (c2 + 4 * i) 1 e1 BS ltac:(replace (c2 + 4 * i - Bb + 1) with (c2 - Bb + 4 * i + 1) by lia; exact M1) ltac:(lia) ltac:(lia)) as RD1.
      pose proof (ade_byte m Bb bs (c2 + 4 * i) 2 e2 BS ltac:(replace (c2 + 4 * i - Bb + 2) with (c2 - Bb + 4 * i + 2) by lia; exact M2) ltac:(lia) ltac:(lia)) as RD2.
      pose proof (ade_byte m Bb bs (c2 + 4 * i) 3 e3 BS ltac:(replace (c2 + 4 * i - Bb + 3) with (c2 - Bb + 4 * i + 3) by lia; exact M3) ltac:(lia) ltac:(lia)) as RD3.
      pose proof (abyte_range e0) as E0R. pose proof (abyte_range e1) as E1R. pose proof (abyte_range e2) as E2R. pose proof (abyte_range e3) as E3R.
      go.
      ck1_load ACCB (c2 + 4 * i) v1 V1 V2 H1.
      ck_K 13 0x553c64 K1.
      { intros tv1. red_tset. clear V1 V2. go.
        ck1_load ACCB (c2 + 4 * i + 3) v2 W1 W2 H2.
        (* [comment removed for export] *)
        ck_K 7 0x553c78 K2.
        { intros tv2. red_tset. clear W1 W2. go.
          change (zxb e0) with (Z_to_bv 64 (bv_unsigned e0)). change (zxb e1) with (Z_to_bv 64 (bv_unsigned e1)).
          change (zxb e2) with (Z_to_bv 64 (bv_unsigned e2)). change (zxb e3) with (Z_to_bv 64 (bv_unsigned e3)).
          reaccS ACCS0 MU ACCS1.
          ck2_load ACCS1 (SA + 6 * i) v3 X1 X2 H3.
          ck_K 31 0x553cbc K3.
          { intros tv3. red_tset. clear X1 X2.
            match goal with SCx : rw_cells asegs ?mx (SA + 6 * i) [CB _ junk] |- _ =>
              (* [comment removed for export] *)
              pose proof (rw_cells_split_CB asegs mx (SA + 6 * i) [] (Z.to_nat (6 * (ns - i))) junk [] [6%nat; Z.to_nat (6 * (ns - (i + 1)))] SCx ltac:(cbn [sum_nat]; lia)) as SC2;
              clear SCx; cbn [mk_CB_cells app] in SC2 end.
            set (Q := SA + 6 * i) in *.
            clear ACCS1 ACCB ACCS ACCE. st1.
            go.
            reaccS ACCS0 MU ACCS2.
            ck2_load ACCS2 (Q + 2) v4 Y1 Y2 H4.
            ck_K 18 0x553cdc K4.
            { intros tv4. red_tset. clear Y1 Y2. clear ACCS2.
              (* [comment removed for export] *)
              pose proof (ub_kdfK (bv_unsigned e0) (bv_unsigned e1) (bv_unsigned e2) (bv_unsigned e3) E0R E1R E2R E3R) as (KV1 & KV2 & WR & KB1 & KD). cbv zeta in KV1, KV2, WR, KB1, KD.
              set (w := bv_unsigned e0 + bv_unsigned e1 * 2^8 + (bv_unsigned e2 * 2^16 + bv_unsigned e3 * 2^24)) in *.
              step. rewrite (unsigned_lit (bv_unsigned e1)) by lia. rewrite Z.shiftl_mul_pow2 by lia.
              step. rewrite (unsigned_lit (bv_unsigned e2)) by lia. rewrite Z.shiftl_mul_pow2 by lia.
              step. rewrite (unsigned_lit (bv_unsigned e1 * 2 ^ 8)), (unsigned_lit (bv_unsigned e0)) by lia. rewrite (Z.lor_comm (bv_unsigned e1 * 2 ^ 8)), (lor_add_disjoint_uK (bv_unsigned e0) (bv_unsigned e1) 8) by lia.
              step. rewrite (unsigned_lit (bv_unsigned e3)) by lia. rewrite Z.shiftl_mul_pow2 by lia.
              step. rewrite (unsigned_lit (bv_unsigned e3 * 2 ^ 24)), (unsigned_lit (bv_unsigned e2 * 2 ^ 16)) by lia.
              rewrite (Z.lor_comm (bv_unsigned e3 * 2 ^ 24)), (lor_add_disjoint_uK (bv_unsigned e2 * 2 ^ 16) (bv_unsigned e3) 24) by lia.
              step. rewrite (unsigned_lit (bv_unsigned e2 * 2 ^ 16 + bv_unsigned e3 * 2 ^ 24)), (unsigned_lit (bv_unsigned e0 + bv_unsigned e1 * 2 ^ 8)) by lia.
              (* [comment removed for export] *)
              rewrite (Z.lor_comm (bv_unsigned e2 * 2 ^ 16 + bv_unsigned e3 * 2 ^ 24)).
              replace (bv_unsigned e2 * 2 ^ 16 + bv_unsigned e3 * 2 ^ 24) with ((bv_unsigned e2 + bv_unsigned e3 * 2 ^ 8) * 2 ^ 16) by lia.
              rewrite (lor_add_disjoint_uK (bv_unsigned e0 + bv_unsigned e1 * 2 ^ 8) (bv_unsigned e2 + bv_unsigned e3 * 2 ^ 8) 16) by lia.
              replace (bv_unsigned e0 + bv_unsigned e1 * 2 ^ 8 + (bv_unsigned e2 + bv_unsigned e3 * 2 ^ 8) * 2 ^ 16) with w by (subst w; lia).
              step. rewrite (unsigned_lit w) by lia. rewrite (Z.shiftl_mul_pow2 w 8) by lia.
              step. rewrite (unsigned_lit w) by lia. step. rewrite (Z.shiftr_div_pow2 _ 56) by lia. rewrite (ub_byte1K w) by lia. rewrite KB1.
              step. rewrite (unsigned_lit (w * 2 ^ 8)), (unsigned_lit (bv_unsigned e1)) by lia. rewrite (Z.lor_comm (w * 2 ^ 8)), (lor_add_disjoint_uK (bv_unsigned e1) w 8) by lia.
              step. st1. go.
              reaccS ACCS0 MU ACCS3.
              (* [comment removed for export] *)
              ck2_load ACCS3 (Q + 4) v5 Z1 Z2 H5.
              ck_K 30 0x553d1c K5.
              { intros tv5. red_tset. clear Z1 Z2. clear ACCS3.
                step. rewrite (unsigned_lit w) by lia. rewrite (Z.shiftr_div_pow2 w 16) by lia. rewrite KD.
                step. rewrite (unsigned_lit (bv_unsigned e2 + 256 * bv_unsigned e3)) by lia. rewrite Z.shiftl_mul_pow2 by lia.
                step. rewrite (unsigned_lit ((bv_unsigned e2 + 256 * bv_unsigned e3) * 2 ^ 8)), (unsigned_lit (bv_unsigned e3)) by lia.
                rewrite (Z.lor_comm ((bv_unsigned e2 + 256 * bv_unsigned e3) * 2 ^ 8)), (lor_add_disjoint_uK (bv_unsigned e3) (bv_unsigned e2 + 256 * bv_unsigned e3) 8) by lia.
                st1.
                reaccS ACCE0 MU ACCE1.
                (* [comment removed for export] *)
                ck4_load ACCE1 (ee + 32) v6 U1 U2 H6.
                ck_K 13 0x553d34 K6.
                { intros tv6. red_tset. clear U1 U2. clear ACCE1.
                  step. rewrite NSQ. unfold zx32. rewrite wz_unsigned by lia. rewrite (Z.mod_small ns) by lia.
                  step. replace (i - 1 + 1) with i by lia. step. step.
                  step. if_cases K0; zify_cond K0; [| exfalso; revert K0; rewrite ?unsigned_lit by lia; clear - IL IR; lia]. clear K0.
                  match goal with SCx : rw_cells asegs ?mx Q ?cs |- _ =>
                    assert (SC3' : rw_cells asegs mx Q ([C2 (Z_to_bv 64 kem); C2 (Z_to_bv 64 (256 * bv_unsigned e0 + bv_unsigned e1)); C2 (Z_to_bv 64 (256 * bv_unsigned e2 + bv_unsigned e3))]
                                                      ++ [CB (Z.to_nat (6 * (ns - (i + 1)))) (firstn (Z.to_nat (6 * (ns - (i + 1)))) (skipn 6 junk))]));
                    (* [comment removed for export] *)
                    [ eapply rw_cells_recutK; [exact SCx| exact (proj1 (proj1 SCx))|];
                      cbn [cells_bytes cbytes app]; rewrite (le2_mod16K (256 * bv_unsigned e0 + bv_unsigned e1) (bv_unsigned e1 + w * 2 ^ 8)) by (clear - KV1 E0R E1R WR; lia);
                      rewrite (le2_mod16K (256 * bv_unsigned e2 + bv_unsigned e3) (bv_unsigned e3 + (bv_unsigned e2 + 256 * bv_unsigned e3) * 2 ^ 8)) by (clear - KV2 E2R E3R; lia); reflexivity
                    | clear SCx ] end.
                  pose proof (proj1 (rw_cells_app asegs _ Q _ _) SC3') as [SC3 SC4]. clear SC3'.
                  cbn [cells_size csize Nat.add] in SC4. subst Q. replace (SA + 6 * i + Z.of_nat 6) with (SA + 6 * (i + 1)) in SC4 by lia.
                  replace (6 * i + 6) with (6 * (i + 1)) by lia.
                  replace (so - 4 * i + -4) with (so - 4 * (i + 1)) in * by lia. replace (c2 + 4 * i + 4) with (c2 + 4 * (i + 1)) in * by lia.
                  replace (Z_to_bv 64 i) with (Z_to_bv 64 (i + 1 - 1)) by (f_equal; lia).
                  (* [comment removed for export] *)
                  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
                    assert (ACCSn : accessible mx SA (6 * ns)) by (unfold id in ACCS0; eapply accessible_across; [exact ACCS0| exact MU|]; repeat (apply Forall_cons; [cbn; unfold AHI_LO, ALOWSH_LO in *; lia|]); apply Forall_nil);
                    assert (ACCEn : accessible mx ee 104) by (unfold id in ACCE0; eapply accessible_across; [exact ACCE0| exact MU|]; repeat (apply Forall_cons; [cbn; unfold AHI_LO, ALOWSH_LO in *; lia|]); apply Forall_nil);
                    assert (ACCBn : accessible mx Bb blen) by (unfold id in ACCB0; eapply accessible_across; [exact ACCB0| exact MU|]; repeat (apply Forall_cons; [cbn; unfold AHI_LO, ALOWSH_LO in *; lia|]); apply Forall_nil) end.
                  eapply evt_mono.
                  { eapply (IH (i + 1)); try eassumption; try (unfold entry_cells; eassumption); try (unfold pk_cells, wz; eassumption); try (unfold wz; eassumption);
                      rewrite ?Nat2Z.inj_succ in HK; try (clear - HK IL IR; lia). all: try (unfold ENTRY_SIZE; lia). all: try (unfold ALOWSH_LO, AHI_LO; lia).
                    all: match goal with |- ?G => idtac "IHLEFT:" G end. }
                  cbv beta. intros ms' (a1' & a3' & u0 & u1 & u2 & s5' & u3 & u4 & u5 & u6 & m1 & junk' & MU1 & WM1 & MI1 & SC5 & FQ1 & ->).
                  (* [comment removed for export] *)
                  exists a1', a3', u0, u1, u2, s5', u3, u4, u5, u6, m1, junk'. repeat match goal with |- _ /\ _ => split end; try assumption.
                  + eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MU1]. intros x Hx. cbn in Hx |- *. lia.
                  + eapply wmono_trans; [exact WM| exact WM1].
                  + cbn [srows asuite_cells app]. replace (Z.to_nat (c2 - Bb + 4 * (i + 1))) with (4 + Z.to_nat (c2 - Bb + 4 * i))%nat in SC5 by lia.
                    unfold bz. replace (Z.to_nat (c2 - Bb + 4 * i)) with (Z.to_nat (c2 - Bb + 4 * i + 0)) by lia. rewrite M0.
                    replace (S (Z.to_nat (c2 - Bb + 4 * i + 0))) with (Z.to_nat (c2 - Bb + 4 * i + 1)) by lia. rewrite M1.
                    replace (S (Z.to_nat (c2 - Bb + 4 * i + 1))) with (Z.to_nat (c2 - Bb + 4 * i + 2)) by lia. rewrite M2.
                    replace (S (Z.to_nat (c2 - Bb + 4 * i + 2))) with (Z.to_nat (c2 - Bb + 4 * i + 3)) by lia. rewrite M3.
                    apply (proj2 (rw_cells_app asegs m1 (SA + 6 * i) [C2 (wz kem); C2 (wz (256 * bv_unsigned e0 + bv_unsigned e1)); C2 (wz (256 * bv_unsigned e2 + bv_unsigned e3))] _)). split.
                    (* [comment removed for export] *)
                    * eapply rw_cells_transport; [exact SC3| exact MU1| exact WM1| cbn; lia].
                    * cbn [cells_size csize Nat.add]. replace (SA + 6 * i + Z.of_nat 6) with (SA + 6 * (i + 1)) by lia. fold bz in SC5.
                      replace (S (S (S (S (Z.to_nat (c2 - Bb + 4 * i + 0)))))) with (4 + Z.to_nat (c2 - Bb + 4 * i))%nat by lia. exact SC5.
                  + reflexivity. }
                ck4_branch_blt (ee + 32) v6 U1 U2 H6 K6. }
              ck2_branch_blt (Q + 4) v5 Z1 Z2 H5 K5. }
            ck2_branch_blt (Q + 2) v4 Y1 Y2 H4 K4. }
          ck2_branch_blt (SA + 6 * i) v3 X1 X2 H3 K3. }
        ck1_branch_blt (c2 + 4 * i + 3) v2 W1 W2 H2 K2. }
      ck1_branch_blt (c2 + 4 * i) v1 V1 V2 H1 K1.
      Unshelve. all: try exact (Z_to_bv 64 0); try exact 0.
  Qed.

  (* [comment removed for export] *)
  Lemma ade_seg7 :
    forall (rax gp tp t0 t1 t2 s0w a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (q rr lbp : Z),
      0 <= rr < 2^64 -> 0 <= lbp < 2^64 ->
      rw_cells asegs m (q + 112) [C8 (wz lbp)] -> aceil <= q -> q + 344 < 2^64 -> mem_inv asegs m ->
      evt asegs (fun ms' =>
            (rr <> 0 /\ ms' = MS (mkR rax (Z_to_bv 64 q) gp tp t0 t1 t2 s0w (Z_to_bv 64 q) (Z_to_bv 64 rr) a1 a2 a3 a4 a5 a6 a7
                                       (Z_to_bv 64 4) s3 (Z_to_bv 64 420) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 F (Z_to_bv 64 ADE_TA) fc None m (seg_rom asegs))
         \/ (rr = 0 /\ ms' = MS (mkR (Z_to_bv 64 ADE_R4a) (Z_to_bv 64 q) gp tp t0 t1 t2 s0w (Z_to_bv 64 q) (Z_to_bv 64 (q + 320)) (Z_to_bv 64 lbp) (Z_to_bv 64 1) a3 a4 a5 a6 a7
                                       (Z_to_bv 64 4) s3 (Z_to_bv 64 420) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 F (Z_to_bv 64 BK_copy) fc None m (seg_rom asegs)))
        (MS (mkR rax (Z_to_bv 64 q) gp tp t0 t1 t2 s0w (Z_to_bv 64 q) (Z_to_bv 64 rr) a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 4) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 ADE_J2) fc None m (seg_rom asegs)).
  Proof.
    (* [comment removed for export] *)
    intros until lbp. intros RR LR FL CQ QH MI.
    unfold ADE_J2, ADE_TA, ADE_R4a, BK_copy in *. unfold wz in FL. pose proof aceil_range as ACR. acb.
    (* [comment removed for export] *)
    go.
    if_cases K0; zify_cond K0.
    (* [comment removed for export] *)
    { assert (RN : rr <> 0) by (revert K0; rewrite ?unsigned_lit by lia; intros K0; lia). clear K0.
      go_to ADE_TA. apply evt_done. left. split; [exact RN| reflexivity]. }
    (* [comment removed for export] *)
    assert (RZ : rr = 0) by (revert K0; rewrite ?unsigned_lit by lia; intros K0; lia). clear K0.
    go. step. apply evt_done. right. split; [exact RZ| reflexivity].
  Qed.

  Lemma ade_seg7b :
    forall (rax gp tp t0 t1 t2 s0w a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (q rv ee lbp : Z) (lb : byte) (E : entrep) pad1 pad2 pad3 pad4,
      (rv = 0 \/ rv = 1) -> 0 <= lbp < 2^64 ->
      rw_cells asegs m (q + 112) [C8 (wz lbp)] -> rw_cells asegs m (q + 168) [C8 (wz ee); C8 (wz ASHB)] -> rw_cells asegs m lbp [C1 lb] ->
      rw_cells asegs m ee (entry_cells E pad1 pad2 pad3 pad4) -> 0 < ee -> ee mod 16 = 0 -> ee + ENTRY_SIZE <= aceil -> accessible m ee ENTRY_SIZE ->
      aceil <= q -> q + 344 < 2^64 -> mem_inv asegs m ->
      evt asegs (fun ms' => exists (a0' a2' a3' : word) m1 mx,
          munch [(ee + 48, ee + 49)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
          /\ rw_cells asegs m1 ee (entry_cells (upd_maxname E mx) pad1 pad2 pad3 pad4) /\
         (  (rv = 0 /\ mx = en_maxname E /\
             ms' = MS (mkR rax (Z_to_bv 64 q) gp tp t0 t1 t2 s0w (Z_to_bv 64 q) a0' a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                      F (Z_to_bv 64 ADE_TA) fc None m1 (seg_rom asegs))
         \/ (rv = 1 /\ mx = bv_unsigned lb /\
             ms' = MS (mkR (Z_to_bv 64 ADE_R4b) (Z_to_bv 64 q) gp tp t0 t1 t2 s0w (Z_to_bv 64 q) (Z_to_bv 64 (q + 320)) (Z_to_bv 64 (q + 248)) a2' a3' a4 a5 a6 a7
                           s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                      F (Z_to_bv 64 BK_get1) fc None m1 (seg_rom asegs))))
        (MS (mkR rax (Z_to_bv 64 q) gp tp t0 t1 t2 s0w (Z_to_bv 64 q) (Z_to_bv 64 rv) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 ADE_R4a)) fc None m (seg_rom asegs)).
  Proof.
    (* [comment removed for export] *)
    intros until pad4. intros RV LR FL FE FB EC EEP EEA EEH ACCE CQ QH MI.
    unfold ADE_R4a, ADE_TA, ADE_R4b, BK_get1 in *. unfold ASHB, wz in FL, FE |- *.
    unfold entry_cells in EC |- *. unfold ENTRY_SIZE in EEH, ACCE. pose proof aceil_range as ACR. retpc.
    acb. pose proof ACCE as (_ & AHIE & _). unfold AAPP_HI in AHIE.
    pose proof (munch_refl [(ee + 48, ee + 49)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    go.
    (* [comment removed for export] *)
    if_cases K0; zify_cond K0.
    { assert (R0 : rv = 0) by (revert K0; rewrite ?unsigned_lit by lia; intros K0; lia). clear K0.
      go_to ADE_TA. apply evt_done. do 3 eexists. eexists. exists (en_maxname E). rewrite upd_maxname_id.
      split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
      left. split; [exact R0| split; [reflexivity| reflexivity]]. }
    assert (R1 : rv = 1) by (revert K0; rewrite ?unsigned_lit by lia; intros K0; lia). clear K0.
    (* [comment removed for export] *)
    go.
    ck1_load ACCE (ee + 48) v1 V1 V2 Ha1.
    step. step. change (zxb lb) with (Z_to_bv 64 (bv_unsigned lb)).
    ck_K 13 0x553e1c K1.
    { intros tv1. red_tset. clear ACCE. go. step.
      apply evt_done. do 3 eexists. eexists. exists (bv_unsigned lb).
      (* [comment removed for export] *)
      split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
      split; [unfold upd_maxname; cbn [en_version en_pname en_pname_o en_publen en_pub en_pub_o en_nsuites en_suites en_suites_o en_maxname en_cfgid en_exts en_exts_o en_loadtime en_forretry en_enclen en_encoded en_encoded_o en_id];
        pose proof (abyte_range lb) as LBR; lazymatch goal with H : rw_cells _ ?mx ?eex (C2 _ :: _) |- rw_cells _ _ ?eex _ => rewrite Z.mod_small in H by lia; exact H end|].
      right. split; [exact R1| split; [reflexivity| reflexivity]]. }
    ck1_branch_blt (ee + 48) v1 V1 V2 Ha1 K1.
    Unshelve. all: try exact (Z_to_bv 64 0); try exact 0.
  Qed.

  Lemma ade_seg7c :
    forall (rax gp tp t0 t1 t2 s0w a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (q rv : Z),
      (rv = 0 \/ rv = 1) -> aceil <= q -> q + 344 < 2^64 ->
      evt asegs (fun ms' =>
            (rv = 0 /\ ms' = MS (mkR rax (Z_to_bv 64 q) gp tp t0 t1 t2 s0w (Z_to_bv 64 q) (Z_to_bv 64 rv) a1 a2 a3 a4 a5 a6 a7
                                       s2 s3 (Z_to_bv 64 425) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 F (Z_to_bv 64 ADE_TA) fc None m (seg_rom asegs))
         \/ (rv = 1 /\ ms' = MS (mkR (Z_to_bv 64 ADE_R4c) (Z_to_bv 64 q) gp tp t0 t1 t2 s0w (Z_to_bv 64 q) (Z_to_bv 64 (q + 248)) a1 a2 a3 a4 a5 a6 a7
                                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 F (Z_to_bv 64 BK_has0) fc None m (seg_rom asegs)))
        (MS (mkR rax (Z_to_bv 64 q) gp tp t0 t1 t2 s0w (Z_to_bv 64 q) (Z_to_bv 64 rv) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 ADE_R4b)) fc None m (seg_rom asegs)).
  Proof.
    (* [comment removed for export] *)
    intros until rv. intros RV CQ QH.
    unfold ADE_R4b, ADE_TA, ADE_R4c, BK_has0 in *. pose proof aceil_range as ACR. acb. retpc.
    go.
    if_cases K0; zify_cond K0.
    (* [comment removed for export] *)
    { assert (R0 : rv = 0) by (revert K0; rewrite ?unsigned_lit by lia; intros K0; lia). clear K0.
      go_to ADE_TA. apply evt_done. left. split; [exact R0| reflexivity]. }
    assert (R1 : rv = 1) by (revert K0; rewrite ?unsigned_lit by lia; intros K0; lia). clear K0.
    go. step. apply evt_done. right. split; [exact R1| reflexivity].
  Qed.

  (* [comment removed for export] *)
  Lemma ade_seg8 :
    forall (rax gp tp t0 t1 t2 s0w a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (q hv c ms len ee : Z),
      (hv = 0 \/ hv = 1) -> 0 <= len < 2^64 -> 0 <= ee -> ee + 8 < 2^64 ->
      rw_cells asegs m (q + 248) (pk_cells c ms len) -> rw_cells asegs m (q + 168) [C8 (wz ee)] ->
      aceil <= q -> q + 344 < 2^64 -> mem_inv asegs m ->
      evt asegs (fun ms' =>
            ((hv <> 0 \/ len < 4) /\ exists a0' : word,
               ms' = MS (mkR rax (Z_to_bv 64 q) gp tp t0 t1 t2 s0w (Z_to_bv 64 q) a0' a1 a2 a3 a4 a5 a6 a7
                             (Z_to_bv 64 4) s3 (Z_to_bv 64 431) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 ADE_TA) fc None m (seg_rom asegs))
         \/ (hv = 0 /\ 4 <= len /\
               ms' = MS (mkR (Z_to_bv 64 ADE_R5) (Z_to_bv 64 q) gp tp t0 t1 t2 s0w (Z_to_bv 64 q) (Z_to_bv 64 (q + 248)) (Z_to_bv 64 (ee + 8)) a2 a3 a4 a5 a6 a7
                             (Z_to_bv 64 4) s3 (Z_to_bv 64 431) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 P_PACKET_strndup) fc None m (seg_rom asegs)))
        (MS (mkR rax (Z_to_bv 64 q) gp tp t0 t1 t2 s0w (Z_to_bv 64 q) (Z_to_bv 64 hv) a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 4) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 ADE_R4c)) fc None m (seg_rom asegs)).
  Proof.
    (* [comment removed for export] *)
    intros until ee. intros HV LR E0 EH FQ FE CQ QH MI.
    unfold ADE_R4c, ADE_TA, ADE_R5, P_PACKET_strndup in *. unfold pk_cells, wz in FQ, FE. pose proof aceil_range as ACR. acb. retpc.
    go.
    if_cases K0; zify_cond K0.
    (* [comment removed for export] *)
    { assert (HN : hv <> 0) by (revert K0; rewrite ?unsigned_lit by lia; intros K0; lia). clear K0.
      go_to ADE_TA. apply evt_done. left. split; [left; exact HN| eexists; reflexivity]. }
    assert (HZ : hv = 0) by (revert K0; rewrite ?unsigned_lit by lia; intros K0; lia). clear K0.
    go.
    (* [comment removed for export] *)
    if_cases K0; zify_cond K0.
    { assert (LN : len < 4) by (revert K0; rewrite ?unsigned_lit by lia; intros K0; lia). clear K0.
      go_to ADE_TA. apply evt_done. left. split; [right; exact LN| eexists; reflexivity]. }
    assert (L4 : 4 <= len) by (revert K0; rewrite ?unsigned_lit by lia; intros K0; lia). clear K0.
    go. step. apply evt_done. right. split; [exact HZ| split; [exact L4| reflexivity]].
  Qed.

  (* [comment removed for export] *)
  Lemma bsg_cut : forall m q (w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : word),
    rw_cells asegs m (q + 144) (arp_sg2 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232) ->
    rw_cells asegs m (q + 240) (arp_sg3 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12) ->
    rw_cells asegs m (q + 144) [C8 w144; C8 w152; C8 w160; C8 w168; C8 w176; C8 w184; C8 w192; C8 w200; C8 w208; C8 w216]
    /\ rw_cells asegs m (q + 224) [C8 w224; C8 w232; C8 x0]
    /\ rw_cells asegs m (q + 248) [C8 x1; C8 x2; C8 x3; C8 x4; C8 x5; C8 x6; C8 x7; C8 x8; C8 x9]
    /\ rw_cells asegs m (q + 320) [C8 x10; C8 x11; C8 x12].
  Proof.
    intros until x12. intros F2 F3. unfold arp_sg2, arp_sg3 in F2, F3.
    change (rw_cells asegs m (q + 144) ([C8 w144; C8 w152; C8 w160; C8 w168; C8 w176; C8 w184; C8 w192; C8 w200; C8 w208; C8 w216] ++ [C8 w224; C8 w232])) in F2.
    change (rw_cells asegs m (q + 240) ([C8 x0] ++ ([C8 x1; C8 x2; C8 x3; C8 x4; C8 x5; C8 x6; C8 x7; C8 x8; C8 x9] ++ [C8 x10; C8 x11; C8 x12]))) in F3.
    apply (proj1 (rw_cells_app _ _ _ _ _)) in F2. destruct F2 as [A1 A2].
    apply (proj1 (rw_cells_app _ _ _ _ _)) in F3. destruct F3 as [B0 B3].
    apply (proj1 (rw_cells_app _ _ _ _ _)) in B3. destruct B3 as [B1 B2].
    cbn [cells_size csize Nat.add] in A2, B1, B2.
    change (Z.of_nat 80) with 80 in A2. change (Z.of_nat 8) with 8 in B1, B2. change (Z.of_nat 72) with 72 in B2.
    replace (q + 144 + 80) with (q + 224) in A2 by lia.
    replace (q + 240 + 8) with (q + 248) in B1, B2 by lia.
    replace (q + 248 + 72) with (q + 320) in B2 by lia.
    split; [exact A1|]. split; [| split; [exact B1| exact B2]].
    change (rw_cells asegs m (q + 224) ([C8 w224; C8 w232] ++ [C8 x0])).
    apply (proj2 (rw_cells_app _ _ _ _ _)). cbn [cells_size csize Nat.add]. change (Z.of_nat 16) with 16.
    replace (q + 224 + 16) with (q + 240) by lia. split; [exact A2| exact B0].
  Qed.

  Lemma bsg_glue : forall m q (w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : word),
    rw_cells asegs m (q + 144) [C8 w144; C8 w152; C8 w160; C8 w168; C8 w176; C8 w184; C8 w192; C8 w200; C8 w208; C8 w216] ->
    rw_cells asegs m (q + 224) [C8 w224; C8 w232; C8 x0] ->
    rw_cells asegs m (q + 248) [C8 x1; C8 x2; C8 x3; C8 x4; C8 x5; C8 x6; C8 x7; C8 x8; C8 x9] ->
    rw_cells asegs m (q + 320) [C8 x10; C8 x11; C8 x12] ->
    rw_cells asegs m (q + 144) (arp_sg2 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232)
    /\ rw_cells asegs m (q + 240) (arp_sg3 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12).
  Proof.
    intros until x12. intros A1 AQ B1 B2.
    change (rw_cells asegs m (q + 224) ([C8 w224; C8 w232] ++ [C8 x0])) in AQ.
    apply (proj1 (rw_cells_app _ _ _ _ _)) in AQ. destruct AQ as [A2 B0].
    cbn [cells_size csize Nat.add] in B0. change (Z.of_nat 16) with 16 in B0. replace (q + 224 + 16) with (q + 240) in B0 by lia.
    split.
    - unfold arp_sg2.
      change (rw_cells asegs m (q + 144) ([C8 w144; C8 w152; C8 w160; C8 w168; C8 w176; C8 w184; C8 w192; C8 w200; C8 w208; C8 w216] ++ [C8 w224; C8 w232])).
      apply (proj2 (rw_cells_app _ _ _ _ _)). cbn [cells_size csize Nat.add]. change (Z.of_nat 80) with 80.
      replace (q + 144 + 80) with (q + 224) by lia. split; [exact A1| exact A2].
    - unfold arp_sg3.
      change (rw_cells asegs m (q + 240) ([C8 x0] ++ ([C8 x1; C8 x2; C8 x3; C8 x4; C8 x5; C8 x6; C8 x7; C8 x8; C8 x9] ++ [C8 x10; C8 x11; C8 x12]))).
      apply (proj2 (rw_cells_app _ _ _ _ _)). cbn [cells_size csize Nat.add]. change (Z.of_nat 8) with 8.
      replace (q + 240 + 8) with (q + 248) by lia. split; [exact B0|].
      apply (proj2 (rw_cells_app _ _ _ _ _)). cbn [cells_size csize Nat.add]. change (Z.of_nat 72) with 72.
      replace (q + 248 + 72) with (q + 320) by lia. split; [exact B1| exact B2].
  Qed.

  (* [comment removed for export] *)
  Lemma ade_seg9 :
    forall (rax gp tp t0 t1 t2 s0w a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (q lo Bb blen nm nl rleft rv ee : Z) (bs : list byte)
           (w144 w152 w160 w176 w184 w192 w200 w208 w216 v224 v232 : word) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : word),
      rw_cells asegs m (q + 144) (arp_sg2 w144 w152 w160 (wz ee) w176 w184 w192 w200 w208 w216 v224 v232) ->
      rw_cells asegs m (q + 240) (arp_sg3 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 (wz (nm + nl)) (wz Bb) (wz (rleft - nl))) ->
      accessible m (q + 224) 24 -> accessible m (q + 320) 24 ->
      bytes_at asegs m Bb bs -> 0 < Bb -> Bb <= nm -> 0 <= nl -> nl <= rleft -> nm + rleft <= Bb + zlength bs -> Bb + zlength bs <= aceil ->
      accessible m Bb blen -> zlength bs <= blen -> 0 <= rv <= 1 ->
      q mod 8 = 0 -> stk asegs m lo q -> aceil <= lo -> lo <= q - 16 -> q + 344 < 2^64 -> mem_inv asegs m -> ACONST m ->
      evt asegs (fun ms' => exists (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m1 (v224' v232' x0' x10' x11' x12' : word) (line : Z),
          munch [(q + -16, q); (q + 320, q + 344); (q + 224, q + 248)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo q
          /\ rw_cells asegs m1 (q + 144) (arp_sg2 w144 w152 w160 (wz ee) w176 w184 w192 w200 w208 w216 v224' v232')
          /\ rw_cells asegs m1 (q + 240) (arp_sg3 x0' x1 x2 x3 x4 x5 x6 x7 x8 x9 x10' x11' x12') /\
         (  ((line = 431 \/ line = 442) /\
             ms' = MS (mkR ra' (Z_to_bv 64 q) gp tp t0' t1' t2' s0w (Z_to_bv 64 q) a0' a1' a2' a3' a4' a5' a6' a7'
                           s2 s3 (Z_to_bv 64 line) s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                      F (Z_to_bv 64 ADE_TA) fc None m1 (seg_rom asegs))
         \/ (exists xl, rv = 1 /\ nl + 2 <= rleft /\ xl = 256 * bz bs (Z.to_nat (nm - Bb + nl)) + bz bs (Z.to_nat (nm - Bb + nl + 1)) /\ nl + 2 + xl <= rleft /\
             v224' = wz (nm + nl + 2) /\ v232' = wz Bb /\ x0' = wz xl /\ x10' = wz (nm + nl + 2 + xl) /\ x11' = wz Bb /\ x12' = wz (rleft - nl - 2 - xl) /\
             (  (xl = 0 /\
                 ms' = MS (mkR ra' (Z_to_bv 64 q) gp tp t0' t1' t2' s0w (Z_to_bv 64 q) a0' a1' a2' a3' a4' a5' a6' a7'
                               s2 s3 (Z_to_bv 64 431) s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                          F (Z_to_bv 64 ADE_J3) fc None m1 (seg_rom asegs))
             \/ (1 <= xl /\
                 ms' = MS (mkR (Z_to_bv 64 ADE_R6) (Z_to_bv 64 q) gp tp t0' t1' t2' s0w (Z_to_bv 64 q) (Z_to_bv 64 ee) (Z_to_bv 64 (q + 224)) a2' a3' a4' a5' a6' a7'
                               s2 s3 (Z_to_bv 64 431) s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                          F (Z_to_bv 64 P_ech_decode_echconfig_exts) fc None m1 (seg_rom asegs))))))
        (MS (mkR rax (Z_to_bv 64 q) gp tp t0 t1 t2 s0w (Z_to_bv 64 q) (Z_to_bv 64 rv) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 (Z_to_bv 64 431) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 ADE_R5)) fc None m (seg_rom asegs)).
  Proof.
    intros until x9. intros FB FC ACCQ ACCP BS BP BNM NL0 NLR NMR BH ACCB BL RVR Q8 ST CEIL LO QH MI AC.
    unfold ADE_R5, ADE_TA, ADE_J3, ADE_R6, P_ech_decode_echconfig_exts in *. retpc.
    acb. pose proof (bytes_at_bound _ _ _ _ BS) as BB. unfold zlength in *. pose proof aceil_range as ACR.
    pose proof ACCB as (_ & AHIB & _). unfold AAPP_HI in AHIB.
    pose proof (munch_refl [(q + -16, q); (q + 320, q + 344); (q + 224, q + 248)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    (* [comment removed for export] *)
    go. if_cases K0; zify_cond K0.
    { (* [comment removed for export] *)
      assert (R0 : rv = 0) by (revert K0; rewrite ?unsigned_lit by lia; lia). clear K0.
      apply evt_done. do 16 eexists. exists m. exists v224, v232, x0, (wz (nm + nl)), (wz Bb), (wz (rleft - nl)), 431.
      repeat match goal with |- _ /\ _ => split end; try eassumption.
      left. split; [left; reflexivity| reflexivity]. }
    assert (R1 : rv = 1) by (revert K0; rewrite ?unsigned_lit by lia; lia). clear K0. subst rv.
    (* [comment removed for export] *)
    go. step.
    destruct (bsg_cut _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FB FC) as (G1 & GQ & G3 & GP). clear FB FC.
    eapply evt_cut.
    { eapply bk_get2_spec with (P := q + 320) (Q := q + 224) (Bb := Bb) (cur := nm + nl) (ms := Bb) (rem := rleft - nl) (lo := lo) (blen := blen) (bs := bs);
        rewrite ?unsigned_lit by lia;
        first [ exact GQ | unfold pk_cells; exact GP | unfold apart; lia | eassumption | reflexivity | lia | unfold zlength; lia ]. }
    (* [comment removed for export] *)
    cbv beta. intros ms1 PO.
    destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & rv2 & MU1 & WM1 & MI1 & ST1 & AC1 & RC & ->).
    retpc. rewrite unsigned_lit in MU1, ST1 by lia. aland MU1 WM1.
    destruct RC as [(R0 & GP' & GQ') | (R2 & len & hi & lb & HIR & LBR & LEN & L2 & N0 & N1 & GP' & GQ')].
    { (* [comment removed for export] *)
      subst rv2. unfold pk_cells in GP'.
      destruct (bsg_glue _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ G1 GQ' G3 GP') as [H2 H3].
      go_to ADE_TA.
      apply evt_done. do 16 eexists. exists m'. do 6 eexists. exists 442.
      repeat match goal with |- _ /\ _ => split end; try eassumption.
      left. split; [right; reflexivity| reflexivity]. }
    subst rv2. unfold pk_cells in GP', GQ'.
    assert (N0' : nth_error bs (Z.to_nat (nm - Bb + nl)) = Some (Z_to_bv 8 hi)) by (rewrite <- N0; f_equal; f_equal; lia).
    assert (N1' : nth_error bs (Z.to_nat (nm - Bb + nl + 1)) = Some (Z_to_bv 8 lb)) by (rewrite <- N1; f_equal; f_equal; lia).
    assert (BZ0 : bz bs (Z.to_nat (nm - Bb + nl)) = hi) by (unfold bz; rewrite N0'; rewrite Z_to_bv_unsigned; apply bv_wrap_small; unfold bv_modulus; lia).
    assert (BZ1 : bz bs (Z.to_nat (nm - Bb + nl + 1)) = lb) by (unfold bz; rewrite N1'; rewrite Z_to_bv_unsigned; apply bv_wrap_small; unfold bv_modulus; lia).
    clear N0 N1 N0' N1'.
    destruct (bsg_glue _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ G1 GQ' G3 GP') as [H2 H3].
    (* [comment removed for export] *)
    go. if_cases K0; zify_cond K0.
    - assert (X0 : len = 0) by (revert K0; rewrite ?unsigned_lit by lia; lia). clear K0.
      apply evt_done. do 16 eexists. exists m'. do 6 eexists. exists 431.
      repeat match goal with |- _ /\ _ => split end; try eassumption.
      right. exists len. rewrite BZ0, BZ1. repeat match goal with |- _ /\ _ => split end; try reflexivity; try lia.
      left. split; [exact X0| reflexivity].
    - assert (X1 : 1 <= len) by (revert K0; rewrite ?unsigned_lit by lia; lia). clear K0.
      (* [comment removed for export] *)
      go. step.
      apply evt_done. do 16 eexists. exists m'. do 6 eexists. exists 431.
      repeat match goal with |- _ /\ _ => split end; try eassumption.
      right. exists len. rewrite BZ0, BZ1. repeat match goal with |- _ /\ _ => split end; try reflexivity; try lia.
      right. split; [exact X1| reflexivity].
    Unshelve. all: try exact (Z_to_bv 64 0); try exact 0.
  Qed.

  (* [comment removed for export] *)
  Lemma ade_seg10 :
    forall (rax gp tp t0 t1 t2 s0w a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (q rv : Z),
      0 <= rv <= 1 -> 0 <= q -> q + 312 < 2^64 -> mem_inv asegs m ->
      evt asegs (fun ms' =>
            (rv = 0 /\
             ms' = MS (mkR rax (Z_to_bv 64 q) gp tp t0 t1 t2 s0w (Z_to_bv 64 q) (Z_to_bv 64 rv) a1 a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 447) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                      F (Z_to_bv 64 ADE_TA) fc None m (seg_rom asegs))
         \/ (rv = 1 /\
             ms' = MS (mkR rax (Z_to_bv 64 q) gp tp t0 t1 t2 s0w (Z_to_bv 64 q) (Z_to_bv 64 rv) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                      F (Z_to_bv 64 ADE_J3) fc None m (seg_rom asegs)))
        (MS (mkR rax (Z_to_bv 64 q) gp tp t0 t1 t2 s0w (Z_to_bv 64 q) (Z_to_bv 64 rv) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 ADE_R6)) fc None m (seg_rom asegs)).
  Proof.
    intros until rv. intros RVR Q0 QH MI. unfold ADE_R6, ADE_TA, ADE_J3 in *. retpc.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
    go. if_cases K0; zify_cond K0.
    - assert (R0 : rv = 0) by (revert K0; rewrite ?unsigned_lit by lia; lia). clear K0.
      go_to ADE_TA. apply evt_done. left. split; [exact R0| reflexivity].
    - assert (R1 : rv = 1) by (revert K0; rewrite ?unsigned_lit by lia; lia). clear K0.
      apply evt_done. right. split; [exact R1| reflexivity].
  Qed.

  (* [comment removed for export] *)
  Lemma ade_seg11 :
    forall (rax gp tp t0 t1 t2 s0w a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (q cur xs xl ee : Z) (E : entrep) pad1 pad2 pad3 pad4
           (w144 w152 w160 w184 w192 w200 w208 w216 w224 w232 : word) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x11 x12 : word),
      rw_cells asegs m (q + 144) (arp_sg2 w144 w152 w160 (wz ee) (wz ASHB) w184 w192 w200 w208 w216 w224 w232) ->
      rw_cells asegs m (q + 240) (arp_sg3 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 (wz (xs + xl)) x11 x12) ->
      0 <= cur <= xs -> 0 <= xl -> xs + xl < 2^64 ->
      rw_cells asegs m ee (entry_cells E pad1 pad2 pad3 pad4) -> 0 < ee -> ee + ENTRY_SIZE <= aceil -> accessible m ee ENTRY_SIZE ->
      aceil <= q -> q + 344 < 2^64 -> mem_inv asegs m ->
      evt asegs (fun ms' => exists m1,
          munch [(ee + 88, ee + 96)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
          /\ rw_cells asegs m1 ee (entry_cells (upd_enclen E (xs + xl - cur)) pad1 pad2 pad3 pad4)
          /\ ms' = MS (mkR (Z_to_bv 64 ADE_R7) (Z_to_bv 64 q) gp tp t0 t1 t2 s0w (Z_to_bv 64 q)
                        (Z_to_bv 64 cur) (Z_to_bv 64 (xs + xl - cur)) (Z_to_bv 64 ADE_FILE) (Z_to_bv 64 453) a4 a5 a6 a7
                        (Z_to_bv 64 ee) s3 s4 s5 s6 s7 (Z_to_bv 64 cur) s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_CRYPTO_memdup) fc None m1 (seg_rom asegs))
        (MS (mkR rax (Z_to_bv 64 q) gp tp t0 t1 t2 s0w (Z_to_bv 64 q) a0 a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 (Z_to_bv 64 cur) s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 ADE_J3) fc None m (seg_rom asegs)).
  Proof.
    intros until x12. intros FB FC CX XL0 XH EC EEP EEH ACCE CQ QH MI.
    unfold ADE_J3, ADE_R7, ADE_FILE, P_CRYPTO_memdup in *. unfold arp_sg2, arp_sg3, ASHB, wz in FB, FC |- *.
    unfold entry_cells in EC |- *. unfold ENTRY_SIZE in EEH, ACCE.
    acb. pose proof ACCE as (_ & AHIE & _). unfold AAPP_HI in AHIE.
    pose proof (munch_refl [(ee + 88, ee + 96)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    (* [comment removed for export] *)
    go. ck8_load ACCE (ee + 88). go.
    (* [comment removed for export] *)
    clear ACCE. go. step.
    (* [comment removed for export] *)
    apply evt_done. eexists. repeat match goal with |- _ /\ _ => split end; try eassumption.
    match goal with |- ?G => first [reflexivity | idtac "ST11:" G] end.
  Qed.

  (* [comment removed for export] *)
  Lemma ade_seg12 :
    forall (rax gp tp t0 t1 t2 s0w a1 a2 a3 a4 a5 a6 a7 s3x s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (q D ee : Z) (E : entrep) pad1 pad2 pad3 pad4
           (w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w128 w136 : word) (w144 w152 w160 w184 w192 w200 w208 w216 w224 w232 : word),
      rw_cells asegs m (q + 16) (arp_sg1 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 (wz 0) w128 w136) ->
      rw_cells asegs m (q + 144) (arp_sg2 w144 w152 w160 (wz ee) (wz ASHB) w184 w192 w200 w208 w216 w224 w232) ->
      0 <= D < 2^64 ->
      rw_cells asegs m ee (entry_cells E pad1 pad2 pad3 pad4) -> 0 < ee -> ee + ENTRY_SIZE <= aceil -> accessible m ee ENTRY_SIZE ->
      aceil <= q -> q + 312 < 2^64 -> mem_inv asegs m ->
      evt asegs (fun ms' => exists m1,
          munch [(ee + 96, ee + 104)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
          /\ rw_cells asegs m1 ee (entry_cells (upd_encoded E D (en_encoded_o E)) pad1 pad2 pad3 pad4) /\
         (  (D = 0 /\
             ms' = MS (mkR rax (Z_to_bv 64 q) gp tp t0 t1 t2 s0w (Z_to_bv 64 q) (Z_to_bv 64 0) (Z_to_bv 64 (ee + 96)) (Z_to_bv 64 0) (Z_to_bv 64 ASHB) a4 a5 a6 a7
                           (Z_to_bv 64 ee) s3x s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                      F (Z_to_bv 64 ADE_TZ) fc None m1 (seg_rom asegs))
         \/ (0 < D /\
             ms' = MS (mkR (Z_to_bv 64 ADE_R8) (Z_to_bv 64 q) gp tp t0 t1 t2 s0w (Z_to_bv 64 q) (Z_to_bv 64 0) (Z_to_bv 64 (ee + 96)) (Z_to_bv 64 0) (Z_to_bv 64 ASHB) a4 a5 a6 a7
                           (Z_to_bv 64 ee) s3x s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                      F (Z_to_bv 64 P_time) fc None m1 (seg_rom asegs))))
        (MS (mkR rax (Z_to_bv 64 q) gp tp t0 t1 t2 s0w (Z_to_bv 64 q) (Z_to_bv 64 D) a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 ee) s3x s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 ADE_R7)) fc None m (seg_rom asegs)).
  Proof.
    intros until w232. intros FA FB DR EC EEP EEH ACCE CQ QH MI.
    unfold ADE_R7, ADE_TZ, ADE_R8, P_time in *. unfold arp_sg1, arp_sg2, ASHB, wz in FA, FB |- *.
    unfold entry_cells in EC |- *. unfold ENTRY_SIZE in EEH, ACCE. retpc.
    acb. pose proof ACCE as (_ & AHIE & _). unfold AAPP_HI in AHIE.
    pose proof (munch_refl [(ee + 96, ee + 104)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    (* [comment removed for export] *)
    go. ck8_load ACCE (ee + 96). go. clear ACCE. go.
    if_cases K0; zify_cond K0.
    { assert (D0 : D = 0) by (revert K0; rewrite ?unsigned_lit by lia; lia). clear K0. subst D.
      apply evt_done. eexists. repeat match goal with |- _ /\ _ => split end; try eassumption. left. split; [reflexivity| reflexivity]. }
    assert (DP : 0 < D) by (revert K0; rewrite ?unsigned_lit by lia; lia). clear K0.
    (* [comment removed for export] *)
    go. step.
    apply evt_done. eexists. repeat match goal with |- _ /\ _ => split end; try eassumption. right. split; [exact DP|].
    match goal with |- ?G => first [reflexivity | idtac "ST12:" G] end.
  Qed.

  (* [comment removed for export] *)
  Lemma ade_seg13 :
    forall (rax gp tp t0 t1 t2 s0w a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (q SH tm ee : Z) (E : entrep) pad1 pad2 pad3 pad4 (w152 w160 w184 w192 w200 w208 w216 w224 w232 : word)
           (sa : list byte) (sb : byte) (sc : list byte) (sb2 sc2 : byte) (sd se : list byte) (sr : byte) (sg : list byte),
      set_shadow_f8_stmt ->
      rw_cells asegs m (q + 144) (arp_sg2 (wz (SH + 10)) w152 w160 (wz ee) (wz ASHB) w184 w192 w200 w208 w216 w224 w232) ->
      rw_cells asegs m SH (arp_fshadow sa sb sc sb2 sc2 sd se sr sg) ->
      ASHB + AIMG_TOP / 8 <= SH -> SH + 512 < AHI_LO -> 0 <= tm < 2^64 ->
      rw_cells asegs m ee (entry_cells E pad1 pad2 pad3 pad4) -> 0 < ee -> ee + ENTRY_SIZE <= aceil -> accessible m ee ENTRY_SIZE -> aapp ee ENTRY_SIZE ->
      aceil <= q -> q + 312 < 2^64 -> mem_inv asegs m -> ACONST m ->
      evt asegs (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m1,
          ms' = MS (mkR (Z_to_bv 64 ADE_R10) (Z_to_bv 64 q) gp tp t0' t1' t2' s0w (Z_to_bv 64 q) (Z_to_bv 64 ee) a1' a2' a3' a4' a5' a6' a7'
                       (Z_to_bv 64 ee) (Z_to_bv 64 SH) s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                   F (Z_to_bv 64 P_ech_final_config_checks) fc None m1 (seg_rom asegs)
          /\ munch [(ee + 64, ee + 72); (SH + 4, SH + 5); (SH + 8, SH + 9); (SH + 10, SH + 266)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
          /\ rw_cells asegs m1 ee (entry_cells (upd_loadtime E tm) pad1 pad2 pad3 pad4)
          /\ rw_cells asegs m1 SH (arp_fshadow sa (b8 248) sc (b8 248) sc2 (poison_bytes 256 248) se sr sg)
          /\ ACONST m1)
        (MS (mkR rax (Z_to_bv 64 q) gp tp t0 t1 t2 s0w (Z_to_bv 64 q) (Z_to_bv 64 tm) a1 a2 a3 a4 a5 a6 a7
                 s2 (Z_to_bv 64 SH) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 ADE_R8)) fc None m (seg_rom asegs)).
  Proof.
    intros until sg. intros SF8 FB FS SH1 SH2 TMR EC EEP EEH ACCE AAPE CQ QH MI AC. pose proof (aapp_not_shadowland _ _ AAPE) as NSE.
    unfold ADE_R8, ADE_R10, P_ech_final_config_checks in *. unfold arp_sg2, ASHB, wz in FB |- *. unfold arp_fshadow in FS |- *.
    unfold entry_cells in EC |- *. unfold ENTRY_SIZE in EEH, ACCE, NSE. unfold ALOWSH_LO, AHI_LO in NSE. retpc.
    unfold ASHB, AIMG_TOP in SH1. unfold AHI_LO in SH2. pose proof aceil_range as ACR.
    acb. pose proof ACCE as (_ & AHIE & _). unfold AAPP_HI in AHIE.
    pose proof (munch_refl [(ee + 64, ee + 72); (SH + 4, SH + 5); (SH + 8, SH + 9); (SH + 10, SH + 266)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    (* [comment removed for export] *)
    pose proof FS as FS0. change (id (rw_cells asegs m SH [CB 4 sa; C1 sb; CB 3 sc; C1 sb2; C1 sc2; CB 256 sd; CB 16 se; C1 sr; CB 229 sg])) in FS0. clear FS.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => pose proof (munch_refl [(ee + 64, ee + 72)] mx) as MUe; pose proof (wmono_refl asegs mx) as WMe end.
    go. ck8_load ACCE (ee + 64). go. clear ACCE.
    (* [comment removed for export] *)
    unfold id in FS0. eapply rw_cells_transport in FS0; [| exact MUe| exact WMe| cbn; change (Z.of_nat 512) with 512; lia]. clear MUe WMe.
    lazymatch type of FS0 with rw_cells _ ?mx _ _ => change (rw_cells asegs mx SH ([CB 4 sa; C1 sb; CB 3 sc; C1 sb2; C1 sc2] ++ (CB 256 sd :: [CB 16 se; C1 sr; CB 229 sg]))) in FS0 end.
    apply (proj1 (rw_cells_app _ _ _ _ _)) in FS0. destruct FS0 as [SH3 SHR4]. cbn [cells_size csize Nat.add] in SHR4. change (Z.of_nat 10) with 10 in SHR4.
    lazymatch type of SHR4 with rw_cells _ ?mx _ _ => change (rw_cells asegs mx (SH + 10) ([CB 256 sd] ++ [CB 16 se; C1 sr; CB 229 sg])) in SHR4 end.
    apply (proj1 (rw_cells_app _ _ _ _ _)) in SHR4. destruct SHR4 as [SH256 SHT]. cbn [cells_size csize Nat.add] in SHT. change (Z.of_nat 256) with 256 in SHT.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      assert (ACc : ACONST mc) by
        (eapply ACONST_frame; [exact AC| exact MU| exact WM|];
         apply Forall_cons; [eapply aconst_ok_aapp; [exact AAPE| cbn; lia| cbn; unfold ENTRY_SIZE; lia]|];
         repeat (apply Forall_cons; [apply aconst_ok_high; cbn [fst snd]; unfold sh, AIMG_TOP; rewrite ?ASHADOW_BASE_val; lia|]); apply Forall_nil) end.
    step. eapply evt_cut.
    { unfold set_shadow_f8_stmt, set_shadow_stmt in SF8. eapply SF8 with (n := 256); [reflexivity| reflexivity| lia| change (Z.to_nat 256) with 256%nat; exact SH256| assumption| exact ACc]. }
    cbv beta. intros ms1 PO. unfold set_shadow_post in PO.
    destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & mA & -> & MU1 & WM1 & MI1 & SH256').
    retpc. clear SH256. aland MU1 WM1.
    (* [comment removed for export] *)
    go. step.
    (* [comment removed for export] *)
    finish.
    { lazymatch goal with |- rw_cells _ ?mx SH _ =>
        lazymatch goal with A : rw_cells _ mx SH [_; _; _; _; _], B : rw_cells _ mx (SH + 10) [_], C : rw_cells _ mx (SH + 10 + 256) _ |- _ =>
            change (Z.to_nat 256) with 256%nat in B;
            pose proof (proj2 (rw_cells_app asegs mx (SH + 10) [CB 256 (poison_bytes 256 248)] _) (conj B ltac:(cbn [cells_size csize Nat.add]; change (Z.of_nat 256) with 256; exact C))) as BC;
            cbn [app] in BC;
            pose proof (proj2 (rw_cells_app asegs mx SH _ _) (conj A ltac:(cbn [cells_size csize Nat.add]; change (Z.of_nat 10) with 10; exact BC))) as ABC;
            cbn [app] in ABC; first [exact ABC | match type of ABC with ?T => idtac "ABC:" T end; match goal with |- ?G => idtac "G:" G end] end end. }
    eapply ACONST_frame; [exact AC| exact MU| exact WM|].
    apply Forall_cons; [eapply aconst_ok_aapp; [exact AAPE| cbn; lia| cbn; unfold ENTRY_SIZE; lia]|].
    repeat (apply Forall_cons; [apply aconst_ok_high; cbn [fst snd]; unfold sh, AIMG_TOP; rewrite ?ASHADOW_BASE_val; lia|]). apply Forall_nil.
  Qed.

  (* [comment removed for export] *)
  Lemma ade_seg14 :
    forall (rax gp tp t0 t1 t2 s0w a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (q frv es h z1 z2 : Z)
           (w16 w24 w32 w40 w48 w64 w72 w80 w88 w96 w104 w112 w120 w136 : word) (w144 w152 w160 w168 w184 w192 w200 w208 w216 w224 w232 : word),
      rw_cells asegs m (q + 16) (arp_sg1 w16 w24 w32 w40 w48 (wz 0) w64 w72 w80 w88 w96 w104 w112 w120 (wz es) w136) ->
      rw_cells asegs m (q + 144) (arp_sg2 w144 w152 w160 w168 (wz ASHB) w184 w192 w200 w208 w216 w224 w232) ->
      rw_cells asegs m es [C8 (wz h); C8 (wz z1); C8 (wz z2)] -> 0 < es -> es + STORE_SIZE <= aceil -> accessible m es STORE_SIZE ->
      0 <= frv <= 1 -> 0 <= h < 2^64 ->
      aceil <= q -> q + 312 < 2^64 -> mem_inv asegs m ->
      evt asegs (fun ms' =>
            (frv = 0 /\
             ms' = MS (mkR rax (Z_to_bv 64 q) gp tp t0 t1 t2 s0w (Z_to_bv 64 q) (Z_to_bv 64 frv) a1 a2 a3 a4 a5 a6 a7
                           w184 s3 s4 s5 s6 w88 w152 w168 w160 w80 t3 t4 t5 t6)
                      F (Z_to_bv 64 ADE_TX2) fc None m (seg_rom asegs))
         \/ (frv = 1 /\ h <> 0 /\
             ms' = MS (mkR rax (Z_to_bv 64 q) gp tp t0 t1 t2 s0w (Z_to_bv 64 q) (Z_to_bv 64 h) a1 a2 a3 a4 a5 a6 a7
                           (Z_to_bv 64 (Z.shiftr es 3 + ASHB)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                      F (Z_to_bv 64 ADE_PUSH) fc None m (seg_rom asegs))
         \/ (frv = 1 /\ h = 0 /\
             ms' = MS (mkR (Z_to_bv 64 ADE_R11) (Z_to_bv 64 q) gp tp t0 t1 t2 s0w (Z_to_bv 64 q) (Z_to_bv 64 h) a1 a2 a3 a4 a5 a6 a7
                           (Z_to_bv 64 (Z.shiftr es 3 + ASHB)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                      F (Z_to_bv 64 P_OPENSSL_sk_new_null) fc None m (seg_rom asegs)))
        (MS (mkR rax (Z_to_bv 64 q) gp tp t0 t1 t2 s0w (Z_to_bv 64 q) (Z_to_bv 64 frv) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 ADE_R10)) fc None m (seg_rom asegs)).
  Proof.
    intros until w232. intros FA FB SC ESP ESH ACCS FRR HR CQ QH MI.
    unfold ADE_R10, ADE_TX2, ADE_PUSH, ADE_R11, P_OPENSSL_sk_new_null in *. unfold arp_sg1, arp_sg2, ASHB, wz in FA, FB, SC |- *. unfold STORE_SIZE in ESH, ACCS. retpc.
    acb. pose proof ACCS as (_ & AHIS & _). unfold AAPP_HI in AHIS.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
    (* [comment removed for export] *)
    go. if_cases K0; zify_cond K0.
    { (* [comment removed for export] *)
      assert (F0 : frv = 0) by (revert K0; rewrite ?unsigned_lit by lia; lia). clear K0.
      go_to ADE_TX2.
      apply evt_done. left. split; [exact F0| reflexivity]. }
    assert (F1 : frv = 1) by (revert K0; rewrite ?unsigned_lit by lia; lia). clear K0.
    (* [comment removed for export] *)
    go. ck8_load ACCS es. go. if_cases K0; zify_cond K0.
    { assert (HNZ : h <> 0) by (revert K0; rewrite ?unsigned_lit by lia; lia). clear K0.
      go_to ADE_PUSH. apply evt_done. right; left. split; [exact F1|]. split; [exact HNZ| reflexivity]. }
    assert (HZ : h = 0) by (revert K0; rewrite ?unsigned_lit by lia; lia). clear K0.
    (* [comment removed for export] *)
    go. step. apply evt_done. right; right. split; [exact F1|]. split; [exact HZ| reflexivity].
  Qed.

  (* [comment removed for export] *)
  Lemma ade_seg15 :
    forall (rax gp tp t0 t1 t2 s0w a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (q sk : Z),
      0 <= sk < 2^64 -> 0 <= q -> q + 312 < 2^64 -> mem_inv asegs m ->
      evt asegs (fun ms' =>
          ms' = MS (mkR (Z_to_bv 64 ADE_R12) (Z_to_bv 64 q) gp tp t0 t1 t2 s0w (Z_to_bv 64 q) (Z_to_bv 64 sk) (Z_to_bv 64 ATH_CMP) a2 a3 a4 a5 a6 a7
                       s2 s3 (Z_to_bv 64 sk) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 P_OPENSSL_sk_set_cmp_thunks) fc None m (seg_rom asegs))
        (MS (mkR rax (Z_to_bv 64 q) gp tp t0 t1 t2 s0w (Z_to_bv 64 q) (Z_to_bv 64 sk) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 ADE_R11)) fc None m (seg_rom asegs)).
  Proof.
    intros until sk. intros SKR Q0 QH MI. unfold ADE_R11, ADE_R12, ATH_CMP, P_OPENSSL_sk_set_cmp_thunks in *. retpc.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
    go. step. apply evt_done. reflexivity.
  Qed.
  (* [comment removed for export] *)
  Lemma ade_seg16 :
    forall (rax gp tp t0 t1 t2 s0w a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (q sk : Z),
      0 <= sk < 2^64 -> 0 <= q -> q + 312 < 2^64 -> mem_inv asegs m ->
      evt asegs (fun ms' =>
          ms' = MS (mkR (Z_to_bv 64 ADE_R13) (Z_to_bv 64 q) gp tp t0 t1 t2 s0w (Z_to_bv 64 q) (Z_to_bv 64 sk) (Z_to_bv 64 ATH_COPY) a2 a3 a4 a5 a6 a7
                       s2 s3 (Z_to_bv 64 sk) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 P_OPENSSL_sk_set_copy_thunks) fc None m (seg_rom asegs))
        (MS (mkR rax (Z_to_bv 64 q) gp tp t0 t1 t2 s0w (Z_to_bv 64 q) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 sk) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 ADE_R12)) fc None m (seg_rom asegs)).
  Proof.
    intros until sk. intros SKR Q0 QH MI. unfold ADE_R12, ADE_R13, ATH_COPY, P_OPENSSL_sk_set_copy_thunks in *. retpc.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
    go. step. apply evt_done. reflexivity.
  Qed.
  (* [comment removed for export] *)
  Lemma ade_seg17 :
    forall (rax gp tp t0 t1 t2 s0w a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (q sk : Z),
      0 <= sk < 2^64 -> 0 <= q -> q + 312 < 2^64 -> mem_inv asegs m ->
      evt asegs (fun ms' =>
          ms' = MS (mkR (Z_to_bv 64 ADE_R14) (Z_to_bv 64 q) gp tp t0 t1 t2 s0w (Z_to_bv 64 q) (Z_to_bv 64 sk) (Z_to_bv 64 ATH_FREE) a2 a3 a4 a5 a6 a7
                       s2 s3 (Z_to_bv 64 sk) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 P_OPENSSL_sk_set_thunks) fc None m (seg_rom asegs))
        (MS (mkR rax (Z_to_bv 64 q) gp tp t0 t1 t2 s0w (Z_to_bv 64 q) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 sk) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 ADE_R13)) fc None m (seg_rom asegs)).
  Proof.
    intros until sk. intros SKR Q0 QH MI. unfold ADE_R13, ADE_R14, ATH_FREE, P_OPENSSL_sk_set_thunks in *. retpc.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
    go. step. apply evt_done. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma ade_f53x :
    forall (rax gp tp t0 t1 t2 s0w a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (q line : Z)
           (w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 : word) (w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 : word),
      rw_cells asegs m (q + 16) (arp_sg1 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136) ->
      rw_cells asegs m (q + 144) (arp_sg2 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232) ->
      0 <= q -> q + 312 < 2^64 -> mem_inv asegs m ->
      evt asegs (fun ms' =>
          ms' = MS (mkR rax (Z_to_bv 64 q) gp tp t0 t1 t2 s0w (Z_to_bv 64 q) a0 a1 a2 a3 a4 a5 a6 a7
                       w184 s3 w24 (Z_to_bv 64 line) s6 w88 w152 w168 w160 w80 t3 t4 t5 t6)
                   F (Z_to_bv 64 ADE_TX) fc None m (seg_rom asegs))
        (MS (mkR rax (Z_to_bv 64 q) gp tp t0 t1 t2 s0w (Z_to_bv 64 q) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 (Z_to_bv 64 line) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x554324) fc None m (seg_rom asegs)).
  Proof.
    intros until w232. intros FA FB Q0 QH MI. unfold ADE_TX in *. unfold arp_sg1, arp_sg2, ASHB, wz in FA, FB |- *.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
    go_to ADE_TX. apply evt_done. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma ade_seg18 :
    forall (rax gp tp t0 t1 t2 s0w a1 a2 a3 a4 a5 a6 a7 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (q sk es z1 z2 h : Z)
           (w16 w24 w32 w40 w48 w64 w72 w80 w88 w96 w104 w112 w120 w136 : word) (w144 w152 w160 w168 w184 w192 w200 w208 w216 w224 w232 : word),
      rw_cells asegs m (q + 16) (arp_sg1 w16 w24 w32 w40 w48 (wz 0) w64 w72 w80 w88 w96 w104 w112 w120 (wz es) w136) ->
      rw_cells asegs m (q + 144) (arp_sg2 w144 w152 w160 w168 (wz ASHB) w184 w192 w200 w208 w216 w224 w232) ->
      rw_cells asegs m es [C8 (wz h); C8 (wz z1); C8 (wz z2)] -> 0 < es -> es + STORE_SIZE <= aceil -> accessible m es STORE_SIZE ->
      0 <= sk < 2^64 ->
      aceil <= q -> q + 312 < 2^64 -> mem_inv asegs m ->
      evt asegs (fun ms' => exists m1,
          munch [(es, es + 8)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
          /\ rw_cells asegs m1 es [C8 (wz sk); C8 (wz z1); C8 (wz z2)] /\
         (  (sk = 0 /\
             ms' = MS (mkR rax (Z_to_bv 64 q) gp tp t0 t1 t2 s0w (Z_to_bv 64 q) (Z_to_bv 64 sk) (Z_to_bv 64 es) a2 a3 a4 a5 a6 a7
                           w184 s3 w24 (Z_to_bv 64 534) s6 w88 w152 w168 w160 w80 t3 t4 t5 t6)
                      F (Z_to_bv 64 ADE_TX) fc None m1 (seg_rom asegs))
         \/ (0 < sk /\
             ms' = MS (mkR rax (Z_to_bv 64 q) gp tp t0 t1 t2 s0w (Z_to_bv 64 q) (Z_to_bv 64 sk) (Z_to_bv 64 es) a2 a3 a4 a5 a6 a7
                           (Z_to_bv 64 (Z.shiftr es 3 + ASHB)) s3 (Z_to_bv 64 sk) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                      F (Z_to_bv 64 ADE_PUSH) fc None m1 (seg_rom asegs))))
        (MS (mkR rax (Z_to_bv 64 q) gp tp t0 t1 t2 s0w (Z_to_bv 64 q) (Z_to_bv 64 sk) a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 (Z.shiftr es 3 + ASHB)) s3 (Z_to_bv 64 sk) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 ADE_R14)) fc None m (seg_rom asegs)).
  Proof.
    intros until w232. intros FA FB SC ESP ESH ACCS SKR CQ QH MI.
    unfold ADE_R14, ADE_TX, ADE_PUSH in *. unfold arp_sg1, arp_sg2, ASHB, wz in FA, FB, SC |- *. unfold STORE_SIZE in ESH, ACCS. retpc.
    acb. pose proof ACCS as (_ & AHIS & _). unfold AAPP_HI in AHIS.
    pose proof (munch_refl [(es, es + 8)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    (* [comment removed for export] *)
    go. ck8_load ACCS es. go. clear ACCS. go. if_cases K0; zify_cond K0.
    - assert (SK0 : sk = 0) by (revert K0; rewrite ?unsigned_lit by lia; lia). clear K0.
      (* [comment removed for export] *)
      go_to ADE_TX.
      apply evt_done. eexists. repeat match goal with |- _ /\ _ => split end; try eassumption. left. split; [exact SK0| reflexivity].
    - assert (SKP : 0 < sk) by (revert K0; rewrite ?unsigned_lit by lia; lia). clear K0.
      go_to ADE_PUSH.
      apply evt_done. eexists. repeat match goal with |- _ /\ _ => split end; try eassumption. right. split; [exact SKP| reflexivity].
  Qed.

  (* [comment removed for export] *)
  Lemma ade_segP :
    forall (rax gp tp t0 t1 t2 s0w a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (q stk ee : Z) (w144 w152 w160 w176 w184 w192 w200 w208 w216 w224 w232 : word),
      rw_cells asegs m (q + 144) (arp_sg2 w144 w152 w160 (wz ee) w176 w184 w192 w200 w208 w216 w224 w232) ->
      0 <= stk < 2^64 -> 0 <= ee < 2^64 -> 0 <= q -> q + 312 < 2^64 -> mem_inv asegs m ->
      evt asegs (fun ms' =>
          ms' = MS (mkR (Z_to_bv 64 ADE_R15) (Z_to_bv 64 q) gp tp t0 t1 t2 s0w (Z_to_bv 64 q) (Z_to_bv 64 stk) (Z_to_bv 64 ee) a2 a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 P_OPENSSL_sk_push) fc None m (seg_rom asegs))
        (MS (mkR rax (Z_to_bv 64 q) gp tp t0 t1 t2 s0w (Z_to_bv 64 q) (Z_to_bv 64 stk) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 ADE_PUSH) fc None m (seg_rom asegs)).
  Proof.
    intros until w232. intros FB SR EER Q0 QH MI. unfold ADE_PUSH, ADE_R15, P_OPENSSL_sk_push in *. unfold arp_sg2, wz in FB.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
    go. step. apply evt_done. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma ade_seg20 :
    forall (rax gp tp t0 t1 t2 s0w a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (q prv : Z)
           (w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 : word) (w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 : word),
      rw_cells asegs m (q + 16) (arp_sg1 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136) ->
      rw_cells asegs m (q + 144) (arp_sg2 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232) ->
      0 <= prv < 2^64 ->
      0 <= q -> q + 312 < 2^64 -> mem_inv asegs m ->
      evt asegs (fun ms' =>
            (prv = 0 /\
             ms' = MS (mkR rax (Z_to_bv 64 q) gp tp t0 t1 t2 s0w (Z_to_bv 64 q) (Z_to_bv 64 prv) a1 a2 a3 a4 a5 a6 a7
                           w184 s3 w24 (Z_to_bv 64 538) s6 w88 w152 w168 w160 w80 t3 t4 t5 t6)
                      F (Z_to_bv 64 ADE_TX) fc None m (seg_rom asegs))
         \/ (prv <> 0 /\
             ms' = MS (mkR rax (Z_to_bv 64 q) gp tp t0 t1 t2 s0w (Z_to_bv 64 q) (Z_to_bv 64 prv) a1 a2 a3 a4 a5 a6 a7
                           (Z_to_bv 64 2) s3 w48 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                      F (Z_to_bv 64 ADE_ADV) fc None m (seg_rom asegs)))
        (MS (mkR rax (Z_to_bv 64 q) gp tp t0 t1 t2 s0w (Z_to_bv 64 q) (Z_to_bv 64 prv) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 ADE_R15)) fc None m (seg_rom asegs)).
  Proof.
    intros until w232. intros FA FB PR Q0 QH MI. unfold ADE_R15, ADE_TX, ADE_ADV in *. unfold arp_sg1, arp_sg2, ASHB, wz in FA, FB |- *. retpc.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
    go. if_cases K0; zify_cond K0.
    - assert (P0 : prv = 0) by (revert K0; rewrite ?unsigned_lit by lia; lia). clear K0.
      (* [comment removed for export] *)
      go_to ADE_TX. apply evt_done. left. split; [exact P0| reflexivity].
    - assert (PN : prv <> 0) by (revert K0; rewrite ?unsigned_lit by lia; lia). clear K0.
      (* [comment removed for export] *)
      go_to ADE_ADV. apply evt_done. right. split; [exact PN| reflexivity].
  Qed.

  (* [comment removed for export] *)
  Lemma ade_skip1 :
    forall (rax gp tp t0 t1 t2 s0w a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (q ee : Z)
           (w144 w152 w160 w176 w184 w192 w200 w208 w216 w224 w232 : word)
           (w240 w248 w256 w264 w272 w280 w288 w296 w304 w312 w320 w328 w336 : word),
      rw_cells asegs m (q + 144) (arp_sg2 w144 w152 w160 (wz ee) w176 w184 w192 w200 w208 w216 w224 w232) ->
      rw_cells asegs m (q + 240) (arp_sg3 w240 w248 w256 w264 w272 w280 w288 w296 w304 w312 w320 w328 w336) ->
      0 <= ee < 2^64 -> aceil <= q -> q + 344 < 2^64 -> mem_inv asegs m ->
      evt asegs (fun ms' => exists m1,
          ms' = MS (mkR (Z_to_bv 64 ADE_SK_R1) (Z_to_bv 64 q) gp tp t0 t1 t2 s0w (Z_to_bv 64 q) (Z_to_bv 64 ee) a1 a2 a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_ossl_echstore_entry_free) fc None m1 (seg_rom asegs)
          /\ munch [(q + 320, q + 328); (q + 336, q + 344)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
          /\ rw_cells asegs m1 (q + 240) (arp_sg3 w240 w248 w256 w264 w272 w280 w288 w296 w304 w312 s4 w328 (wz 0)))
        (MS (mkR rax (Z_to_bv 64 q) gp tp t0 t1 t2 s0w (Z_to_bv 64 q) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 ADE_SKIP) fc None m (seg_rom asegs)).
  Proof.
    intros until w336. intros FB FC EER CQ QH MI. unfold ADE_SKIP, ADE_SK_R1, P_ossl_echstore_entry_free in *.
    unfold arp_sg2, arp_sg3, wz in FB, FC |- *. pose proof aceil_range as ACR.
    pose proof (munch_refl [(q + 320, q + 328); (q + 336, q + 344)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    go. step. finish.
  Qed.

  (* [comment removed for export] *)
  Lemma ade_skip2 :
    forall (rax gp tp t0 t1 t2 s0w a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (q SH : Z) (w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 : word)
           (sa : list byte) (sb : byte) (sc : list byte) (sb2 sc2 : byte) (sd se : list byte) (sr : byte) (sg : list byte),
      set_shadow_f8_stmt ->
      rw_cells asegs m (q + 144) (arp_sg2 (wz (SH + 10)) w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232) ->
      rw_cells asegs m SH (arp_fshadow sa sb sc sb2 sc2 sd se sr sg) ->
      ASHB + AIMG_TOP / 8 <= SH -> SH + 512 < AHI_LO ->
      aceil <= q -> q + 344 < 2^64 -> mem_inv asegs m -> ACONST m ->
      evt asegs (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m1,
          ms' = MS (mkR (Z_to_bv 64 ADE_SK_R2) (Z_to_bv 64 q) gp tp t0' t1' t2' s0w (Z_to_bv 64 q) (Z_to_bv 64 (-8)) a1' a2' a3' a4' a5' a6' a7'
                       s2 (Z_to_bv 64 SH) s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                   F (Z_to_bv 64 ADE_ADV) fc None m1 (seg_rom asegs)
          /\ munch [(SH + 4, SH + 5); (SH + 8, SH + 9); (SH + 10, SH + 266)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
          /\ rw_cells asegs m1 SH (arp_fshadow sa (b8 0xf8) sc (b8 0xf8) sc2 (poison_bytes 256 0xf8) se sr sg)
          /\ ACONST m1)
        (MS (mkR rax (Z_to_bv 64 q) gp tp t0 t1 t2 s0w (Z_to_bv 64 q) a0 a1 a2 a3 a4 a5 a6 a7
                 s2 (Z_to_bv 64 SH) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 ADE_SK_R1)) fc None m (seg_rom asegs)).
  Proof.
    intros until sg. intros SF8 FB FS SH1 SH2 CQ QH MI AC.
    unfold ADE_SK_R1, ADE_SK_R2, ADE_ADV in *. unfold arp_sg2, wz in FB |- *. unfold arp_fshadow in FS |- *. retpc.
    let v := eval vm_compute in (AIMG_TOP / 8) in change (AIMG_TOP / 8) with v in SH1.
    unfold ASHB in *. unfold AHI_LO in SH2. pose proof aceil_range as ACR. acb.
    pose proof (munch_refl [(SH + 4, SH + 5); (SH + 8, SH + 9); (SH + 10, SH + 266)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    (* [comment removed for export] *)
    go. step.
    lazymatch goal with FSx : rw_cells asegs ?mx SH (?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?rest) |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      pose proof FSx as SHC; change (rw_cells asegs mx SH ([c1; c2; c3; c4; c5] ++ (c6 :: rest))) in SHC; clear FSx end.
    apply (proj1 (rw_cells_app _ _ _ _ _)) in SHC. destruct SHC as [SH3 SHR4]. cbn [cells_size csize Nat.add] in SHR4. change (Z.of_nat 10) with 10 in SHR4.
    lazymatch type of SHR4 with rw_cells _ ?mx _ (?c4 :: ?rest) => change (rw_cells asegs mx (SH + 10) ([c4] ++ rest)) in SHR4 end.
    apply (proj1 (rw_cells_app _ _ _ _ _)) in SHR4. destruct SHR4 as [SH256 SHT]. cbn [cells_size csize Nat.add] in SHT. change (Z.of_nat 256) with 256 in SHT.
    eapply evt_cut.
    { unfold set_shadow_f8_stmt, set_shadow_stmt in SF8. eapply SF8 with (n := 256); [reflexivity| reflexivity| lia| change (Z.to_nat 256) with 256%nat; exact SH256| assumption| exact AC]. }
    cbv beta. intros ms1 PO. unfold set_shadow_post in PO.
    destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & mA & -> & MU1 & WM1 & MI1 & SH256').
    retpc. clear SH256. aland MU1 WM1.
    (* [comment removed for export] *)
    go_to ADE_ADV.
    finish.
    { lazymatch goal with |- rw_cells _ ?mx ?base _ =>
        lazymatch goal with A : rw_cells _ mx base [_; _; _; _; _], B : rw_cells _ mx (base + 10) [_], C : rw_cells _ mx (base + 10 + 256) _ |- _ =>
            change (Z.to_nat 256) with 256%nat in B;
            pose proof (proj2 (rw_cells_app asegs mx (base + 10) [CB 256 (poison_bytes 256 248)] _) (conj B ltac:(cbn [cells_size csize Nat.add]; change (Z.of_nat 256) with 256; exact C))) as BC;
            cbn [app] in BC;
            pose proof (proj2 (rw_cells_app asegs mx base _ _) (conj A ltac:(cbn [cells_size csize Nat.add]; change (Z.of_nat 10) with 10; exact BC))) as ABC;
            cbn [app] in ABC; exact ABC end end. }
    eapply ACONST_frame; [exact AC| exact MU| exact WM|].
    apply Forall_cons; [apply aconst_ok_high; cbn [fst snd]; unfold sh, AIMG_TOP; rewrite ?ASHADOW_BASE_val; lia|].
    apply Forall_cons; [apply aconst_ok_high; cbn [fst snd]; unfold sh, AIMG_TOP; rewrite ?ASHADOW_BASE_val; lia|].
    apply Forall_cons; [apply aconst_ok_high; cbn [fst snd]; unfold sh, AIMG_TOP; rewrite ?ASHADOW_BASE_val; lia| apply Forall_nil].
  Qed.
End S.
