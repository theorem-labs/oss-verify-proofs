(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Sorting.Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec CellsX TacX Frame SFModel.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.As Require Import ASegs AsShadow AsConst AsIface AsIfaceX AsCXXHeap AsCall AsCallX ECH_AImg ECH_Xpres ECH_ARep ECH_ALib ECH_Iface
  ECH_AStmt_C1 ECH_AStmt_C5 ECH_AStmt_C10 ECH_AStmt_C13 ECH_AKit ECH_AsKit ECH_AsKitK ECH_AC14_decexts_seg ECH_AC14_fcc_seg ECH_AC14_bio2buf_seg.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.As Require Import N6_tac.   (* [comment removed for export] *)
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import StoreDj.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition ADE_AHEAD : Z := 0x51a9fc.  Definition ADE_R0 : Z := 0x51aa18.   Definition ADE_R1 : Z := 0x51aa2c.   Definition ADE_J1 : Z := 0x51aaf8.
Definition ADE_SKIP : Z := 0x51ae68.   Definition ADE_SK_R1 : Z := 0x51ae70. Definition ADE_SK_R2 : Z := 0x51ae84.
Definition ADE_R2 : Z := 0x51ac14.     Definition ADE_R3 : Z := 0x51acbc.   Definition ADE_LH : Z := 0x51ad10.   Definition ADE_J2 : Z := 0x51ae90.
Definition ADE_R4 : Z := 0x51af40.     Definition ADE_R5 : Z := 0x51af60.   Definition ADE_R6 : Z := 0x51afe0.   Definition ADE_J3 : Z := 0x51afe4.
Definition ADE_R7 : Z := 0x51b028.     Definition ADE_OK : Z := 0x51b128.   Definition ADE_R8 : Z := 0x51b134.   Definition ADE_R9 : Z := 0x51b168.
Definition ADE_R10 : Z := 0x51b178.    Definition ADE_R11 : Z := 0x51b1a8.  Definition ADE_R12 : Z := 0x51b1c0.  Definition ADE_R13 : Z := 0x51b1d4.
Definition ADE_R14 : Z := 0x51b1e8.    Definition ADE_PUSH : Z := 0x51b1fc. Definition ADE_R15 : Z := 0x51b208.  Definition ADE_ADV : Z := 0x51b214.
Definition ADE_TA : Z := 0x51b35c.     Definition ADE_TZ : Z := 0x51b394.   Definition ADE_TX : Z := 0x51b3d8.   Definition ADE_TX2 : Z := 0x51b410.
Definition ADE_FCCFAIL : Z := 0x51b47c. Definition ADE_A367 : Z := 0x51b474. Definition ADE_A447 : Z := 0x51b4a0.
Definition ADE_F538 : Z := 0x51b498.   Definition ADE_F534 : Z := 0x51b4b0.
(* [comment removed for export] *)
Definition ADE_FILE : Z := 0x119140.   (* [comment removed for export] *)
Definition AECH_VERSION : Z := 0xfe0d.
Definition ATH_CMP : Z := 0x51b71c. Definition ATH_COPY : Z := 0x51b748. Definition ATH_FREE : Z := 0x51b6f4.   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition arp_fframe2 (q tpl : Z) (j24 tpb j128 : list byte) (rb : Z) (j2 : list byte) (fp : Z) : list cell :=
  [C8 (wz AFRAME_MAGIC); C8 (wz ARP_DESCR); C8 (wz P_ech_read_priv_echconfiglist); C8 (wz q); C8 (wz tpl); CB 24 j24; CB 2048 tpb; CB 128 j128;
   C8 (wz rb); CB 1840 j2; C8 (wz fp)].

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
    forall (rax gp tp t0 t1 t2 s0w a0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s8 s10 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (q ff SH cur rem Bb : Z)
           (w16 w24 w32 w40 w48 w56 w64 w72 w80 w96 w104 w112 w120 w128 w136 : word)
           (w144 w152 w160 w184 w192 w200 w208 w224 w232 : word)
           (tpl rb fp : Z) (j24 tpb j128 j2 : list byte) (sa : list byte) (sb : byte) (sc sd se : list byte) (sr : byte) (sg : list byte),
      set_shadow_00_stmt ->
      rw_cells asegs m (q + 16) (arp_sg1 w16 w24 w32 w40 w48 w56 w64 w72 w80 (wz ADE_FILE) w96 w104 w112 w120 w128 w136) ->
      rw_cells asegs m (q + 144) (arp_sg2 w144 w152 w160 (wz (ff + 32)) (wz (SH + 8)) w184 w192 w200 w208 (wz ASHB) w224 w232) ->
      rw_cells asegs m ff (arp_fframe2 q tpl j24 tpb j128 rb j2 fp) ->
      rw_cells asegs m SH (arp_fshadow sa sb sc sd se sr sg) ->
      ASHB + AIMG_TOP / 8 <= SH -> SH + 512 < AHI_LO -> AIMG_TOP + 32 <= ff -> ff + 4096 <= aceil -> aapp ff 4096 ->
      aceil <= q -> q + 312 < 2^64 ->
      mem_inv asegs m -> ACONST m ->
      evt asegs (fun ms' => exists (t0' t1' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m1,
          ms' = MS (mkR (Z_to_bv 64 ADE_R1) (Z_to_bv 64 q) gp tp t0' t1' t2' s0w (Z_to_bv 64 q)
                       (Z_to_bv 64 104) (Z_to_bv 64 ADE_FILE) (Z_to_bv 64 360) a3' a4' a5' a6' a7'
                       (Z_to_bv 64 cur) (Z_to_bv 64 SH) (Z_to_bv 64 rem) s5 s6 (Z_to_bv 64 ASHB) s8 (Z_to_bv 64 Bb) s10 (Z_to_bv 64 (SH + 8)) t3' t4' t5' t6')
                   F (Z_to_bv 64 P_CRYPTO_zalloc) fc None m1 (seg_rom asegs)
          /\ munch [(SH + 4, SH + 5); (ff + 32, ff + 40); (SH + 8, SH + 264)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
          /\ rw_cells asegs m1 ff (arp_fframe2 q 0 j24 tpb j128 rb j2 fp)
          /\ rw_cells asegs m1 SH (arp_fshadow sa (b8 0) sc (poison_bytes 256 0) se sr sg)
          /\ ACONST m1)
        (MS (mkR rax (Z_to_bv 64 q) gp tp t0 t1 t2 s0w (Z_to_bv 64 q) a0 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 cur) (Z_to_bv 64 SH) (Z_to_bv 64 rem) s5 s6 (Z_to_bv 64 ASHB) s8 (Z_to_bv 64 Bb) s10 (Z_to_bv 64 (SH + 8)) t3 t4 t5 t6)
            F (Z_to_bv 64 ADE_AHEAD) fc None m (seg_rom asegs)).
  Proof.
    intros until sg. intros SF00 FA FB FF FS SH1 SH2 FF1 FF2 AAP CQ QH MI AC.
    unfold ADE_AHEAD, ADE_R1, P_CRYPTO_zalloc in *. unfold arp_sg1, arp_sg2, ADE_FILE, wz in FA, FB |- *. unfold arp_fframe2, wz in FF |- *. unfold arp_fshadow in FS |- *.
    acb. unfold aapp, aapp_lo, aapp_hi, AIMG_TOP, AHI_LO, ALOWSH_LO in AAP, FF1.
    unfold ASHB in *. unfold AIMG_TOP in SH1. unfold AHI_LO in SH2. change (12386304 / 8) with 1548288 in SH1.
    pose proof (munch_refl [(SH + 4, SH + 5); (ff + 32, ff + 40); (SH + 8, SH + 264)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    (* [comment removed for export] *)
    st1. step. st1. step. step. step. step.
    (* [comment removed for export] *)
    lazymatch goal with FSx : rw_cells asegs ?mx SH (?c1 :: ?c2 :: ?c3 :: ?c4 :: ?rest) |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      pose proof FSx as SHC; change (rw_cells asegs mx SH ([c1; c2; c3] ++ (c4 :: rest))) in SHC end.
    apply (proj1 (rw_cells_app _ _ _ _ _)) in SHC. destruct SHC as [SH3 SHR4]. cbn [cells_size csize Nat.add] in SHR4. change (Z.of_nat 8) with 8 in SHR4.
    lazymatch type of SHR4 with rw_cells _ ?mx _ (?c4 :: ?rest) => change (rw_cells asegs mx (SH + 8) ([c4] ++ rest)) in SHR4 end.
    apply (proj1 (rw_cells_app _ _ _ _ _)) in SHR4. destruct SHR4 as [SH256 SHT]. cbn [cells_size csize Nat.add] in SHT. change (Z.of_nat 256) with 256 in SHT.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      assert (ACc : ACONST mc) by
        (eapply ACONST_frame; [exact AC| exact MU| exact WM|];
         apply Forall_cons; [apply aconst_ok_high; cbn [fst snd]; unfold sh, AIMG_TOP; rewrite ?ASHADOW_BASE_val; lia|];
         apply Forall_cons; [eapply aconst_ok_aapp; [exact AAP| cbn; lia| cbn; lia]|];
         apply Forall_cons; [apply aconst_ok_high; cbn [fst snd]; unfold sh, AIMG_TOP; rewrite ?ASHADOW_BASE_val; lia| apply Forall_nil]) end.
    eapply evt_cut.
    { unfold set_shadow_00_stmt, set_shadow_stmt in SF00. eapply SF00 with (n := 256); [reflexivity| reflexivity| lia| change (Z.to_nat 256) with 256%nat; exact SH256| assumption| exact ACc]. }
    cbv beta. intros ms1 PO. unfold set_shadow_post in PO.
    destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & mA & -> & MU1 & WM1 & MI1 & SH256').
    retpc. clear SH256.
    aland MU1 WM1.
    (* [comment removed for export] *)
    step. step. step. step. step.
    finish.
    { (* [comment removed for export] *)
      lazymatch goal with |- rw_cells _ ?mx ?base _ =>
        lazymatch goal with A : rw_cells _ mx base [_; _; _], B : rw_cells _ mx (base + 8) [_], C : rw_cells _ mx (base + 8 + 256) _ |- _ =>
            change (Z.to_nat 256) with 256%nat in B;
            pose proof (proj2 (rw_cells_app asegs mx (base + 8) [CB 256 (poison_bytes 256 0)] _) (conj B ltac:(cbn [cells_size csize Nat.add]; change (Z.of_nat 256) with 256; exact C))) as BC;
            cbn [app] in BC;
            pose proof (proj2 (rw_cells_app asegs mx base _ _) (conj A ltac:(cbn [cells_size csize Nat.add]; change (Z.of_nat 8) with 8; exact BC))) as ABC;
            cbn [app] in ABC; exact ABC end end. }
    eapply ACONST_frame; [exact AC| exact MU| exact WM|].
    apply Forall_cons; [apply aconst_ok_high; cbn [fst snd]; unfold sh, AIMG_TOP; rewrite ?ASHADOW_BASE_val; lia|].
    apply Forall_cons; [eapply aconst_ok_aapp; [exact AAP| cbn; lia| cbn; lia]|].
    apply Forall_cons; [apply aconst_ok_high; cbn [fst snd]; unfold sh, AIMG_TOP; rewrite ?ASHADOW_BASE_val; lia| apply Forall_nil].
  Qed.

  (* [comment removed for export] *)
  Lemma ade_seg2 :
    forall (rax gp tp t0 t1 t2 s0w a1 a2 a3 a4 a5 a6 a7 s5 s6 s8 s10 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (q SH cur rem Bb blen ee : Z) (bs : list byte) (E : entrep) pad1 pad2 pad3 pad4
           (w16 w24 w32 w40 w48 w56 w64 w72 w96 w104 w112 w120 w128 w136 : word)
           (w144 w152 w160 w168 w176 w184 w192 w200 w208 w224 w232 : word),
      rw_cells asegs m (q + 16) (arp_sg1 w16 w24 w32 w40 w48 w56 w64 w72 (wz AECH_VERSION) (wz ADE_FILE) w96 w104 w112 w120 w128 w136) ->
      rw_cells asegs m (q + 144) (arp_sg2 w144 w152 w160 w168 w176 w184 w192 w200 w208 (wz ASHB) w224 w232) ->
      bytes_at asegs m Bb bs -> Bb <= cur -> 1 <= rem -> cur + rem <= Bb + zlength bs -> 0 < Bb -> Bb + zlength bs <= aceil ->
      accessible m Bb blen -> zlength bs <= blen ->
      rw_cells asegs m ee (entry_cells E pad1 pad2 pad3 pad4) -> 0 < ee -> ee + ENTRY_SIZE <= aceil -> (Bb + zlength bs <= ee \/ ee + ENTRY_SIZE <= Bb) ->
      accessible m ee ENTRY_SIZE -> (ee + ENTRY_SIZE <= ALOWSH_LO \/ AHI_LO <= ee) ->
      aceil <= q -> q + 312 < 2^64 -> mem_inv asegs m ->
      evt asegs (fun ms' => exists (a0' a1' a2' a3' a4' a5' a6' : word) m1 (w112' w128' w136' : word) (v : Z),
          munch [(q + 112, q + 152); (ee, ee + 2)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
          /\ rw_cells asegs m1 (q + 16) (arp_sg1 w16 w24 w32 w40 w48 w56 w64 w72 (wz AECH_VERSION) (wz ADE_FILE) w96 w104 w112' w120 w128' w136')
          /\ rw_cells asegs m1 (q + 144) (arp_sg2 (wz ee) w152 w160 w168 w176 w184 w192 w200 w208 (wz ASHB) w224 w232)
          /\ rw_cells asegs m1 ee (entry_cells (upd_version E v) pad1 pad2 pad3 pad4) /\ (v = en_version E \/ 0 <= v < 2^16) /\
         (  (exists (line : Z) (s2' s4' : word), (line = 367 \/ line = 374) /\
             ms' = MS (mkR rax (Z_to_bv 64 q) gp tp t0 t1 t2 s0w (Z_to_bv 64 q) a0' a1' a2' a3' a4' a5' a6' a7
                           s2' (Z_to_bv 64 SH) s4' s5 s6 (Z_to_bv 64 ASHB) s8 (Z_to_bv 64 Bb) s10 (Z_to_bv 64 line) t3 t4 t5 t6)
                      F (Z_to_bv 64 ADE_TA) fc None m1 (seg_rom asegs))
         \/ (exists elen, 0 <= elen /\ 4 + elen <= rem /\ w112' = wz (rem - 4) /\ w128' = wz elen /\ w136' = wz cur /\ 0 <= v < 2^16 /\
             (  (v <> AECH_VERSION /\
                 ms' = MS (mkR rax (Z_to_bv 64 q) gp tp t0 t1 t2 s0w (Z_to_bv 64 q) a0' a1' a2' a3' a4' (Z_to_bv 64 ASHB) (Z_to_bv 64 ee) a7
                               (Z_to_bv 64 (cur + 4)) (Z_to_bv 64 SH) (Z_to_bv 64 (rem - 4)) s5 s6 (Z_to_bv 64 ASHB) s8 (Z_to_bv 64 Bb) s10 (Z_to_bv 64 374) t3 t4 t5 t6)
                          F (Z_to_bv 64 ADE_SKIP) fc None m1 (seg_rom asegs))
             \/ (v = AECH_VERSION /\
                 ms' = MS (mkR rax (Z_to_bv 64 q) gp tp t0 t1 t2 s0w (Z_to_bv 64 q) a0' a1' a2' a3' a4' (Z_to_bv 64 ASHB) (Z_to_bv 64 ee) a7
                               (Z_to_bv 64 (cur + 4)) (Z_to_bv 64 SH) (Z_to_bv 64 (rem - 4)) s5 s6 (Z_to_bv 64 ASHB) s8 (Z_to_bv 64 Bb) s10 (Z_to_bv 64 374) t3 t4 t5 t6)
                          F (Z_to_bv 64 ADE_J1) fc None m1 (seg_rom asegs))))))
        (MS (mkR rax (Z_to_bv 64 q) gp tp t0 t1 t2 s0w (Z_to_bv 64 q) (Z_to_bv 64 ee) a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 cur) (Z_to_bv 64 SH) (Z_to_bv 64 rem) s5 s6 (Z_to_bv 64 ASHB) s8 (Z_to_bv 64 Bb) s10 (Z_to_bv 64 (SH + 8)) t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 ADE_R1)) fc None m (seg_rom asegs)).
  Proof.
    intros until w232. intros FA FB BS BC R1 CR BP BH ACCB BL EC EEP EEH EBA ACCE NSE CQ QH MI.
    unfold ADE_R1, ADE_TA, ADE_SKIP, ADE_J1 in *. unfold arp_sg1, arp_sg2, AECH_VERSION, ADE_FILE, ASHB, wz in FA, FB |- *.
    unfold entry_cells in EC |- *. unfold ENTRY_SIZE in EEH, EBA, ACCE, NSE. unfold ALOWSH_LO, AHI_LO in NSE. retpc. pose proof aceil_range as ACR.
    acb. pose proof (bytes_at_bound _ _ _ _ BS) as BB. unfold zlength in *.
    pose proof ACCB as (_ & AHIB & _). pose proof ACCE as (_ & AHIE & _). unfold AAPP_HI in AHIB, AHIE.
    pose proof (munch_refl [(q + 112, q + 152); (ee, ee + 2)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof ACCB as ACCB0. change (accessible m Bb blen) with (id (accessible m Bb blen)) in ACCB0.
    pose proof ACCE as ACCE0. change (accessible m ee 104) with (id (accessible m ee 104)) in ACCE0.
    (* [comment removed for export] *)
    st1. step. br. step. step. if_cases K0; zify_cond K0.
    { (* [comment removed for export] *)
      assert (R1' : rem = 1) by (revert K0; rewrite ?unsigned_lit by lia; lia). clear K0.
      step. step.
      apply evt_done. do 7 eexists. eexists. exists w112, w128, w136, (en_version E).
      repeat match goal with |- _ /\ _ => split end; try eassumption; try (rewrite upd_version_id; eassumption).
      - left. reflexivity.
      - left. exists 367. do 2 eexists. split; [left; reflexivity| reflexivity]. }
    assert (R2 : 2 <= rem) by (revert K0; rewrite ?unsigned_lit by lia; lia). clear K0.
    destruct (nth_error bs (Z.to_nat (cur - Bb + 0))) as [c0|] eqn:N0; [| apply nth_error_None in N0; lia].
    destruct (nth_error bs (Z.to_nat (cur - Bb + 1))) as [c1|] eqn:N1; [| apply nth_error_None in N1; lia].
    pose proof (ade_byte _ _ _ _ _ _ BS N0 ltac:(lia) ltac:(lia)) as RD0. pose proof (ade_byte _ _ _ _ _ _ BS N1 ltac:(lia) ltac:(lia)) as RD1.
    pose proof (abyte_range c0) as C0R. pose proof (abyte_range c1) as C1R.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (ACCB1 : accessible mx Bb blen) by (unfold id in ACCB0; eapply accessible_across; [exact ACCB0| exact MU|]; apply Forall_cons; [cbn; unfold AHI_LO, ALOWSH_LO in *; lia|]; apply Forall_cons; [cbn; unfold AHI_LO, ALOWSH_LO in *; lia| apply Forall_nil]);
      assert (ACCE1 : accessible mx ee 104) by (unfold id in ACCE0; eapply accessible_across; [exact ACCE0| exact MU|]; apply Forall_cons; [cbn; unfold AHI_LO, ALOWSH_LO in *; lia|]; apply Forall_cons; [cbn; unfold AHI_LO, ALOWSH_LO in *; lia| apply Forall_nil]) end.
    (* [comment removed for export] *)
    zstep. step. zstep. ck1_load ACCB1 cur v1 V1 V2 Hc1.
    ck_K 11 0x51aa50 K1.
    { intros tv1. red_tset.
      (* [comment removed for export] *)
      zstep. zstep. zstep. ck1_load ACCB1 (cur + 1) v2 W1 W2 Hc2.
      step. change (zxb c0) with (Z_to_bv 64 (bv_unsigned c0)). step.
      ck_K 13 0x51aa6c K2.
      { intros tv2. red_tset.
        (* [comment removed for export] *)
        zstep. zstep. ck8_load ACCE1 ee. step. change (zxb c1) with (Z_to_bv 64 (bv_unsigned c1)). step. if_false_by (ck1_bnez_false 0 eq_refl).
        (* [comment removed for export] *)
        step. step. step.
        rewrite Z.shiftl_mul_pow2 by lia. rewrite (unsigned_lit (bv_unsigned c0)) by lia. rewrite (unsigned_lit (bv_unsigned c0 * 2 ^ 8)) by lia. rewrite (unsigned_lit (bv_unsigned c1)) by lia.
        rewrite (be16_lor (bv_unsigned c0) (bv_unsigned c1)) by lia.
        set (v := bv_unsigned c1 + 256 * bv_unsigned c0) in *. assert (VR : 0 <= v < 2^16) by (subst v; lia).
        clear ACCB1 ACCE1. st1.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
          assert (ACCB2 : accessible mx Bb blen) by (unfold id in ACCB0; eapply accessible_across; [exact ACCB0| exact MU|]; apply Forall_cons; [cbn; unfold AHI_LO, ALOWSH_LO in *; lia|]; apply Forall_cons; [cbn; unfold AHI_LO, ALOWSH_LO in *; lia| apply Forall_nil]) end.
        (* [comment removed for export] *)
        step. step. step. if_cases K0; zify_cond K0.
        { (* [comment removed for export] *)
          apply evt_done. do 7 eexists. eexists. exists w112, w128, w136, v.
          repeat match goal with |- _ /\ _ => split end; try eassumption.
          - right. exact VR.
          - left. exists 374. do 2 eexists. split; [right; reflexivity| reflexivity]. }
        assert (R4 : 4 <= rem) by (revert K0; rewrite ?unsigned_lit by lia; rewrite land_even_mask, land_W64, land_1, Z.mod_small by lia; clear - R2; intros K0; lia). clear K0.
        destruct (nth_error bs (Z.to_nat (cur - Bb + 2))) as [c2|] eqn:N2; [| apply nth_error_None in N2; lia].
        destruct (nth_error bs (Z.to_nat (cur - Bb + 3))) as [c3|] eqn:N3; [| apply nth_error_None in N3; lia].
        pose proof (abyte_range c2) as C2R. pose proof (abyte_range c3) as C3R.
        (* [comment removed for export] *)
        zstep. zstep. zstep. ck1_load ACCB2 (cur + 2) v4 X1 X2 Hc4.
        ck_K 13 0x51aab0 K3.
        { intros tv3. red_tset.
          (* [comment removed for export] *)
          zstep. zstep. zstep. ck1_load ACCB2 (cur + 3) v5 Y1 Y2 Hc5.
          clear ACCB2. st1.
          lazymatch goal with BSx : bytes_at asegs ?mx Bb bs |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
            pose proof (ade_byte _ _ _ _ _ _ BSx N2 ltac:(lia) ltac:(lia)) as RD2; pose proof (ade_byte _ _ _ _ _ _ BSx N3 ltac:(lia) ltac:(lia)) as RD3 end.
          step. change (zxb c2) with (Z_to_bv 64 (bv_unsigned c2)).
          ck_K 14 0x51aacc K4.
          { intros tv4. red_tset.
            (* [comment removed for export] *)
            step. change (zxb c3) with (Z_to_bv 64 (bv_unsigned c3)). step. step.
            rewrite Z.shiftl_mul_pow2 by lia. rewrite (unsigned_lit (bv_unsigned c2)) by lia. rewrite (unsigned_lit (bv_unsigned c2 * 2 ^ 8)) by lia. rewrite (unsigned_lit (bv_unsigned c3)) by lia.
            rewrite (be16_lor (bv_unsigned c2) (bv_unsigned c3)) by lia.
            set (elen := bv_unsigned c3 + 256 * bv_unsigned c2) in *. assert (ELR : 0 <= elen < 2^16) by (subst elen; lia).
            zstep. st1. st1.
            (* [comment removed for export] *)
            step. if_cases K0; zify_cond K0.
            { (* [comment removed for export] *)
              assert (RL : rem - 4 < elen) by (revert K0; rewrite ?unsigned_lit by lia; clear - R4 ELR; intros K0; lia). clear K0.
              apply evt_done. do 7 eexists. eexists. exists (Z_to_bv 64 (rem + -4)), (Z_to_bv 64 elen), (Z_to_bv 64 cur), v.
              repeat match goal with |- _ /\ _ => split end; try eassumption.
              - right. exact VR.
              - left. exists 374. do 2 eexists. split; [right; reflexivity| reflexivity]. }
            assert (RL : elen <= rem - 4) by (revert K0; rewrite ?unsigned_lit by lia; clear - R4 ELR; intros K0; lia). clear K0.
            (* [comment removed for export] *)
            step. zstep. step. step. if_cases K0; zify_cond K0.
            - (* [comment removed for export] *)
              assert (NV : v <> 65037) by (revert K0; rewrite ?unsigned_lit by lia; clear - VR; intros K0; lia). clear K0.
              apply evt_done. do 7 eexists. eexists. exists (Z_to_bv 64 (rem + -4)), (Z_to_bv 64 elen), (Z_to_bv 64 cur), v.
              repeat match goal with |- _ /\ _ => split end; try eassumption.
              + right. exact VR.
              + right. exists elen. split; [lia|]. split; [lia|]. split; [unfold wz; f_equal; lia|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact VR|].
                left. split; [exact NV|]. replace (rem + -4) with (rem - 4) by lia. reflexivity.
            - assert (EV : v = 65037) by (revert K0; rewrite ?unsigned_lit by lia; clear - VR; intros K0; lia). clear K0.
              apply evt_done. do 7 eexists. eexists. exists (Z_to_bv 64 (rem + -4)), (Z_to_bv 64 elen), (Z_to_bv 64 cur), v.
              repeat match goal with |- _ /\ _ => split end; try eassumption.
              + right. exact VR.
              + right. exists elen. split; [lia|]. split; [lia|]. split; [unfold wz; f_equal; lia|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact VR|].
                right. split; [exact EV|]. replace (rem + -4) with (rem - 4) by lia. reflexivity. }
          ck1_branch_bge (cur + 3) v5 Y1 Y2 Hc5 K4. }
        ck1_branch_bge (cur + 2) v4 X1 X2 Hc4 K3. }
      ck1_branch_bge (cur + 1) v2 W1 W2 Hc2 K2. }
    ck1_branch_bge cur v1 V1 V2 Hc1 K1.
    Unshelve. all: try exact (Z_to_bv 64 0); try exact 0.
  Qed.

  (* [comment removed for export] *)
  Lemma ade_seg3 :
    forall (rax gp tp t0 t1 t2 s0w a0 a1 a2 a3 a4 a7 s5 s6 s8 s10 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (q SH cur rem elen Bb blen ee : Z) (bs : list byte) (E : entrep) pad1 pad2 pad3 pad4
           (w16 w24 w32 w40 w48 w56 w64 w72 w96 w104 : word)
           (w152 w160 w168 w176 w184 w192 w200 w208 w224 w232 : word) (x0 x1 x2 n0 n1 n2 p0 p1 p2 : word),
      rw_cells asegs m (q + 16) (arp_sg1 w16 w24 w32 w40 w48 w56 w64 w72 (wz AECH_VERSION) (wz ADE_FILE) w96 w104 (wz (rem - 4)) (wz Bb) (wz elen) (wz cur)) ->
      rw_cells asegs m (q + 144) (arp_sg2 (wz ee) w152 w160 w168 w176 w184 w192 w200 w208 (wz ASHB) w224 w232) ->
      rw_cells asegs m (q + 240) (arp_sg3 x0 x1 x2 n0 n1 n2 p0 p1 p2) ->
      bytes_at asegs m Bb bs -> Bb <= cur -> 0 <= elen -> cur + 4 + elen <= Bb + zlength bs -> 0 < Bb -> Bb + zlength bs <= aceil ->
      accessible m Bb blen -> zlength bs <= blen ->
      rw_cells asegs m ee (entry_cells E pad1 pad2 pad3 pad4) -> length pad3 = 6%nat -> 0 < ee -> ee + ENTRY_SIZE <= aceil -> (Bb + zlength bs <= ee \/ ee + ENTRY_SIZE <= Bb) ->
      accessible m ee ENTRY_SIZE -> (ee + ENTRY_SIZE <= ALOWSH_LO \/ AHI_LO <= ee) ->
      aceil <= q -> q + 312 < 2^64 -> mem_inv asegs m ->
      evt asegs (fun ms' => exists (a0' a1' a2' a3' a4' s4' s5' s6' s8' s9' : word) m1 (w24' w32' w40' w56' w64' p0' p1' p2' : word) (cf : Z),
          munch [(q + 24, q + 72); (q + 288, q + 312); (ee + 49, ee + 50)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
          /\ rw_cells asegs m1 (q + 16) (arp_sg1 w16 w24' w32' w40' w48 w56' w64' w72 (wz AECH_VERSION) (wz ADE_FILE) w96 w104 (wz (rem - 4)) (wz Bb) (wz elen) (wz cur))
          /\ rw_cells asegs m1 (q + 240) (arp_sg3 x0 x1 x2 n0 n1 n2 p0' p1' p2')
          /\ rw_cells asegs m1 ee (entry_cells (upd_cfgid E cf) pad1 pad2 pad3 pad4) /\ (cf = en_cfgid E \/ 0 <= cf < 256) /\
         (  ms' = MS (mkR rax (Z_to_bv 64 q) gp tp t0 t1 t2 s0w (Z_to_bv 64 q) a0' a1' a2' a3' a4' (Z_to_bv 64 ASHB) (Z_to_bv 64 ee) a7
                        (Z_to_bv 64 (cur + 4)) (Z_to_bv 64 SH) s4' s5' s6' (Z_to_bv 64 ASHB) s8' s9' s10 (Z_to_bv 64 400) t3 t4 t5 t6)
                   F (Z_to_bv 64 ADE_TA) fc None m1 (seg_rom asegs)
         \/ (exists publen, publen = 256 * bz bs (Z.to_nat (cur - Bb + 7)) + bz bs (Z.to_nat (cur - Bb + 8)) /\ 5 + publen <= elen /\
             cf = bz bs (Z.to_nat (cur - Bb + 4)) /\ w40' = wz (cur + 4) /\ w64' = wz (bz bs (Z.to_nat (cur - Bb + 5))) /\ w56' = wz (bz bs (Z.to_nat (cur - Bb + 6))) /\
             w24' = wz (ee + 24) /\ w32' = wz (ee + 16) /\ p0' = wz (cur + 9) /\ p1' = wz Bb /\ p2' = wz publen /\
             ms' = MS (mkR (Z_to_bv 64 ADE_R2) (Z_to_bv 64 q) gp tp t0 t1 t2 s0w (Z_to_bv 64 q)
                           (Z_to_bv 64 (q + 288)) (Z_to_bv 64 (ee + 24)) (Z_to_bv 64 (ee + 16)) (Z_to_bv 64 ASHB) (Z_to_bv 64 cur) (Z_to_bv 64 ASHB) (Z_to_bv 64 ee) a7
                           (Z_to_bv 64 (cur + 4)) (Z_to_bv 64 SH) (Z_to_bv 64 (bz bs (Z.to_nat (cur - Bb + 8)))) (Z_to_bv 64 (elen - 5)) (Z_to_bv 64 (cur + 9)) (Z_to_bv 64 ASHB)
                           (Z_to_bv 64 (256 * bz bs (Z.to_nat (cur - Bb + 7)))) (Z_to_bv 64 publen) s10 (Z_to_bv 64 400) t3 t4 t5 t6)
                      F (Z_to_bv 64 P_PACKET_memdup) fc None m1 (seg_rom asegs))))
        (MS (mkR rax (Z_to_bv 64 q) gp tp t0 t1 t2 s0w (Z_to_bv 64 q) a0 a1 a2 a3 a4 (Z_to_bv 64 ASHB) (Z_to_bv 64 ee) a7
                 (Z_to_bv 64 (cur + 4)) (Z_to_bv 64 SH) (Z_to_bv 64 (rem - 4)) s5 s6 (Z_to_bv 64 ASHB) s8 (Z_to_bv 64 Bb) s10 (Z_to_bv 64 374) t3 t4 t5 t6)
            F (Z_to_bv 64 ADE_J1) fc None m (seg_rom asegs)).
  Proof.
    intros until p2. intros FA FB FC BS BC EL0 CR BP BH ACCB BL EC L3 EEP EEH EBA ACCE NSE CQ QH MI.
    unfold ADE_J1, ADE_TA, ADE_R2, P_PACKET_memdup in *. unfold arp_sg1, arp_sg2, arp_sg3, AECH_VERSION, ADE_FILE, ASHB, wz in FA, FB, FC |- *.
    unfold entry_cells in EC |- *. unfold ENTRY_SIZE in EEH, EBA, ACCE, NSE. unfold ALOWSH_LO, AHI_LO in NSE. pose proof aceil_range as ACR.
    acb. pose proof (bytes_at_bound _ _ _ _ BS) as BB. unfold zlength in *.
    pose proof ACCB as (_ & AHIB & _). pose proof ACCE as (_ & AHIE & _). unfold AAPP_HI in AHIB, AHIE.
    pose proof (munch_refl [(q + 24, q + 72); (q + 288, q + 312); (ee + 49, ee + 50)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof ACCB as ACCB0. change (accessible m Bb blen) with (id (accessible m Bb blen)) in ACCB0.
    pose proof ACCE as ACCE0. change (accessible m ee 104) with (id (accessible m ee 104)) in ACCE0.
    Local Ltac reaccB ACCB0 MU N := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (N : accessible mx _ _) by (unfold id in ACCB0; eapply accessible_across; [exact ACCB0| exact MU|];
        repeat (apply Forall_cons; [cbn; unfold AHI_LO, ALOWSH_LO in *; lia|]); apply Forall_nil) end.
    Local Ltac exitTA0 := apply evt_done; do 10 eexists; eexists; do 8 eexists; eexists;
      repeat match goal with |- _ /\ _ => split end; [eassumption| eassumption| eassumption| eassumption| eassumption| | | left; reflexivity];
      [| left; reflexivity]; rewrite upd_cfgid_id; eassumption.
    Local Ltac exitTA1 := apply evt_done; do 10 eexists; eexists; do 8 eexists; eexists;
      repeat match goal with |- _ /\ _ => split end; [eassumption| eassumption| eassumption| eassumption| eassumption| | | left; reflexivity];
      [lazymatch goal with H : rw_cells _ ?mx ?eex (C2 _ :: _) |- rw_cells _ _ ?eex _ => rewrite Z.mod_small in H by lia; exact H end|]; right; lia.
    (* [comment removed for export] *)
    step. step. step. if_cases K0; zify_cond K0.
    { (* [comment removed for export] *)
      exitTA0. }
    assert (EL1 : 1 <= elen) by (revert K0; rewrite ?unsigned_lit by lia; lia). clear K0.
    destruct (nth_error bs (Z.to_nat (cur - Bb + 4))) as [c4|] eqn:N4; [| apply nth_error_None in N4; lia]. pose proof (abyte_range c4) as C4R.
    pose proof (ade_byte _ _ _ _ _ _ BS N4 ltac:(lia) ltac:(lia)) as RD4.
    (* [comment removed for export] *)
    replace (cur + 4) with (cur + 4) by lia.
    zstep. zstep. ck1_load ACCB (cur + 4) v6 V1 V2 Hc6.
    ck_K 11 0x51ab14 K1.
    { intros tv1. red_tset.
      (* [comment removed for export] *)
      step. zstep. zstep. zstep. ck8_load ACCE (ee + 49). st1.
      lazymatch goal with BSx : bytes_at asegs ?mx Bb bs |- evt _ _ (MS _ _ _ _ _ ?mx _) => pose proof (ade_byte _ _ _ _ _ _ BSx N4 ltac:(lia) ltac:(lia)) as RD4' end.
      replace (cur + 4 + 0) with (cur + 4) in RD4' by lia.
      step. change (zxb c4) with (Z_to_bv 64 (bv_unsigned c4)). step. if_false_by (ck1_bnez_false 0 eq_refl).
      (* [comment removed for export] *)
      clear ACCB ACCE. st1.
      (* [comment removed for export] *)
      step. step. step. if_cases K0; zify_cond K0.
      { (* [comment removed for export] *)
        exitTA1. }
      assert (EL3 : 3 <= elen) by (revert K0; rewrite ?unsigned_lit by lia; lia). clear K0.
      destruct (nth_error bs (Z.to_nat (cur - Bb + 5))) as [c5|] eqn:N5; [| apply nth_error_None in N5; lia]. pose proof (abyte_range c5) as C5R.
      destruct (nth_error bs (Z.to_nat (cur - Bb + 6))) as [c6|] eqn:N6; [| apply nth_error_None in N6; lia]. pose proof (abyte_range c6) as C6R.
      lazymatch goal with BSx : bytes_at asegs ?mx Bb bs |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
        pose proof (ade_byte _ _ _ _ _ _ BSx N5 ltac:(lia) ltac:(lia)) as RD5; pose proof (ade_byte _ _ _ _ _ _ BSx N6 ltac:(lia) ltac:(lia)) as RD6 end.
      reaccB ACCB0 MU ACCB2.
      (* [comment removed for export] *)
      step. zstep. zstep. step. zstep. ck1_load ACCB2 (cur + 5) v8 W1 W2 Hc8.
      ck_K 12 0x51ab60 K2.
      { intros tv2. red_tset.
        (* [comment removed for export] *)
        zstep. zstep. zstep. ck1_load ACCB2 (cur + 6) v9 X1 X2 Hc9.
        step. change (zxb c5) with (Z_to_bv 64 (bv_unsigned c5)). clear ACCB2. st1.
        ck_K 12 0x51ab7c K3.
        { intros tv3. red_tset.
          (* [comment removed for export] *)
          step. zstep. step. step. if_cases K0; zify_cond K0.
          { (* [comment removed for export] *)
            exitTA1. }
          assert (EL5 : 5 <= elen) by (revert K0; rewrite ?unsigned_lit by lia; lia). clear K0.
          destruct (nth_error bs (Z.to_nat (cur - Bb + 7))) as [c7|] eqn:N7; [| apply nth_error_None in N7; lia]. pose proof (abyte_range c7) as C7R.
          destruct (nth_error bs (Z.to_nat (cur - Bb + 8))) as [c8|] eqn:N8; [| apply nth_error_None in N8; lia]. pose proof (abyte_range c8) as C8R.
          lazymatch goal with BSx : bytes_at asegs ?mx Bb bs |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
            pose proof (ade_byte _ _ _ _ _ _ BSx N6 ltac:(lia) ltac:(lia)) as RD6'; pose proof (ade_byte _ _ _ _ _ _ BSx N7 ltac:(lia) ltac:(lia)) as RD7;
            pose proof (ade_byte _ _ _ _ _ _ BSx N8 ltac:(lia) ltac:(lia)) as RD8 end.
          reaccB ACCB0 MU ACCB3.
          (* [comment removed for export] *)
          step. zstep. zstep. step. zstep. ck1_load ACCB3 (cur + 7) v10 Y1 Y2 Hc10.
          step. change (zxb c6) with (Z_to_bv 64 (bv_unsigned c6)). clear ACCB3. st1.
          ck_K 10 0x51abb0 K4.
          { intros tv4. red_tset.
            lazymatch goal with BSx : bytes_at asegs ?mx Bb bs |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
              pose proof (ade_byte _ _ _ _ _ _ BSx N7 ltac:(lia) ltac:(lia)) as RD7'; pose proof (ade_byte _ _ _ _ _ _ BSx N8 ltac:(lia) ltac:(lia)) as RD8' end.
            reaccB ACCB0 MU ACCB4.
            (* [comment removed for export] *)
            zstep. zstep. zstep. ck1_load ACCB4 (cur + 8) v11 Z1 Z2 Hc11.
            step. change (zxb c7) with (Z_to_bv 64 (bv_unsigned c7)).
            ck_K 12 0x51abc8 K5.
            { intros tv5. red_tset.
              (* [comment removed for export] *)
              step. change (zxb c8) with (Z_to_bv 64 (bv_unsigned c8)). step. step.
              rewrite Z.shiftl_mul_pow2 by lia. rewrite (unsigned_lit (bv_unsigned c7)) by lia. rewrite (unsigned_lit (bv_unsigned c7 * 2 ^ 8)) by lia. rewrite (unsigned_lit (bv_unsigned c8)) by lia.
              rewrite (be16_lor (bv_unsigned c7) (bv_unsigned c8)) by lia.
              set (publen := bv_unsigned c8 + 256 * bv_unsigned c7) in *. assert (PLR : 0 <= publen < 2^16) by (subst publen; lia).
              step. zstep. step. if_cases K0; zify_cond K0.
              { (* [comment removed for export] *)
                exitTA1. }
              assert (PL : 5 + publen <= elen) by (revert K0; rewrite ?unsigned_lit by lia; lia). clear K0.
              (* [comment removed for export] *)
              step. zstep. step. zstep. clear ACCB4. st1. step. st1. st1. zstep. zstep. st1. st1. step.
              apply evt_done. do 10 eexists. eexists. do 8 eexists. eexists.
              repeat match goal with |- _ /\ _ => split end; try eassumption;
                [lazymatch goal with H : rw_cells _ ?mx ?eex (C2 _ :: _) |- rw_cells _ _ ?eex _ => rewrite Z.mod_small in H by lia; exact H end| right; lia|].
              right. exists publen. unfold bz. rewrite N4, N5, N6, N7, N8.
              repeat match goal with |- _ /\ _ => split end; try reflexivity; try lia.
              replace (256 * bv_unsigned c7) with (bv_unsigned c7 * 2 ^ 8) by lia. replace (elen - 5) with (elen + -5) by lia. reflexivity. }
            ck1_branch_bge (cur + 8) v11 Z1 Z2 Hc11 K5. }
          ck1_branch_bge (cur + 7) v10 Y1 Y2 Hc10 K4. }
        ck1_branch_bge (cur + 6) v9 X1 X2 Hc9 K3. }
      ck1_branch_bge (cur + 5) v8 W1 W2 Hc8 K2. }
    ck1_branch_bge (cur + 4) v6 V1 V2 Hc6 K1.
    Unshelve. all: try exact (Z_to_bv 64 0); try exact 0.
  Qed.

  (* [comment removed for export] *)
  Lemma ade_seg4 :
    forall (rax gp tp t0 t1 t2 s0w a1 a2 a3 a4 a5 a6 a7 s10 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (q SH cur elen publen b7 b8 Bb blen ee : Z) (bs : list byte) (E : entrep) pad1 pad2 pad3 pad4
           (w16 w24 w32 w40 w48 w56 w64 w72 w96 w104 w112 w120 w128 w136 : word)
           (w152 w160 w168 w176 w184 w192 w200 w208 w224 w232 : word),
      rw_cells asegs m (q + 16) (arp_sg1 w16 w24 w32 w40 w48 w56 w64 w72 (wz AECH_VERSION) (wz ADE_FILE) w96 w104 w112 w120 w128 w136) ->
      rw_cells asegs m (q + 144) (arp_sg2 (wz ee) w152 w160 w168 w176 w184 w192 w200 w208 (wz ASHB) w224 w232) ->
      bytes_at asegs m Bb bs -> Bb <= cur -> 0 <= publen -> 5 + publen <= elen -> cur + 4 + elen <= Bb + zlength bs -> 0 < Bb -> Bb + zlength bs <= aceil ->
      accessible m Bb blen -> zlength bs <= blen -> 0 <= b7 < 256 -> 0 <= b8 < 256 ->
      rw_cells asegs m ee (entry_cells E pad1 pad2 pad3 pad4) -> 0 < ee -> ee + ENTRY_SIZE <= aceil -> (Bb + zlength bs <= ee \/ ee + ENTRY_SIZE <= Bb) ->
      accessible m ee ENTRY_SIZE -> (ee + ENTRY_SIZE <= ALOWSH_LO \/ AHI_LO <= ee) ->
      aceil <= q -> q + 312 < 2^64 -> mem_inv asegs m ->
      evt asegs (fun ms' => exists (a0' a1' a2' a3' a4' s2' s5' s9' : word) m1 (w48' w72' : word) (ns : Z),
          munch [(q + 48, q + 56); (q + 72, q + 80); (ee + 32, ee + 36)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
          /\ rw_cells asegs m1 (q + 16) (arp_sg1 w16 w24 w32 w40 w48' w56 w64 w72' (wz AECH_VERSION) (wz ADE_FILE) w96 w104 w112 w120 w128 w136)
          /\ rw_cells asegs m1 ee (entry_cells (upd_nsuites E ns) pad1 pad2 pad3 pad4) /\ (ns = en_nsuites E \/ 0 <= ns < 2^14) /\
         (  ms' = MS (mkR rax (Z_to_bv 64 q) gp tp t0 t1 t2 s0w (Z_to_bv 64 q) a0' a1' a2' a3' a4' a5 a6 a7
                        s2' (Z_to_bv 64 SH) (Z_to_bv 64 b8) s5' (Z_to_bv 64 (cur + 9)) (Z_to_bv 64 ASHB) (Z_to_bv 64 (256 * b7)) s9' s10 (Z_to_bv 64 400) t3 t4 t5 t6)
                   F (Z_to_bv 64 ADE_TA) fc None m1 (seg_rom asegs)
         \/ (exists sl, sl = 256 * bz bs (Z.to_nat (cur - Bb + (9 + publen))) + bz bs (Z.to_nat (cur - Bb + (10 + publen))) /\ 1 <= sl /\ sl mod 2 = 0 /\
             7 + publen + sl <= elen /\ ns = sl / 4 /\ w48' = wz (elen - 7 - publen) /\ w72' = wz (bz bs (Z.to_nat (cur - Bb + (10 + publen)))) /\
             ms' = MS (mkR (Z_to_bv 64 ADE_R3) (Z_to_bv 64 q) gp tp t0 t1 t2 s0w (Z_to_bv 64 q)
                           (Z_to_bv 64 ns) (Z_to_bv 64 6) (Z_to_bv 64 ADE_FILE) (Z_to_bv 64 405) a4' a5 a6 a7
                           (Z_to_bv 64 ee) (Z_to_bv 64 SH) (Z_to_bv 64 b8) (Z_to_bv 64 sl) (Z_to_bv 64 (Z.shiftr (ee + 32) 3 + ASHB)) (Z_to_bv 64 ASHB)
                           (Z_to_bv 64 (256 * b7)) (Z_to_bv 64 (cur + 9 + publen)) (Z_to_bv 64 (ee + 32)) (Z_to_bv 64 ns) t3 t4 t5 t6)
                      F (Z_to_bv 64 P_CRYPTO_malloc_array) fc None m1 (seg_rom asegs))))
        (MS (mkR rax (Z_to_bv 64 q) gp tp t0 t1 t2 s0w (Z_to_bv 64 q) (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 (cur + 4)) (Z_to_bv 64 SH) (Z_to_bv 64 b8) (Z_to_bv 64 (elen - 5)) (Z_to_bv 64 (cur + 9)) (Z_to_bv 64 ASHB)
                 (Z_to_bv 64 (256 * b7)) (Z_to_bv 64 publen) s10 (Z_to_bv 64 400) t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 ADE_R2)) fc None m (seg_rom asegs)).
  Proof.
    intros until w232. intros FA FB BS BC PL0 PL CR BP BH ACCB BL B7R B8R EC EEP EEH EBA ACCE NSE CQ QH MI.
    unfold ADE_R2, ADE_TA, ADE_R3, P_CRYPTO_malloc_array in *. unfold arp_sg1, arp_sg2, AECH_VERSION, ADE_FILE, ASHB, wz in FA, FB |- *.
    unfold entry_cells in EC |- *. unfold ENTRY_SIZE in EEH, EBA, ACCE, NSE. unfold ALOWSH_LO, AHI_LO in NSE. pose proof aceil_range as ACR. retpc.
    acb. pose proof (bytes_at_bound _ _ _ _ BS) as BB. unfold zlength in *.
    pose proof ACCB as (_ & AHIB & _). pose proof ACCE as (_ & AHIE & _). unfold AAPP_HI in AHIB, AHIE.
    pose proof (munch_refl [(q + 48, q + 56); (q + 72, q + 80); (ee + 32, ee + 36)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof ACCB as ACCB0. change (accessible m Bb blen) with (id (accessible m Bb blen)) in ACCB0.
    pose proof ACCE as ACCE0. change (accessible m ee 104) with (id (accessible m ee 104)) in ACCE0.
    Local Ltac exit4 := apply evt_done; do 8 eexists; eexists; do 2 eexists; eexists;
      repeat match goal with |- _ /\ _ => split end; [eassumption| eassumption| eassumption| eassumption| | | left; reflexivity];
      [| left; reflexivity]; rewrite upd_nsuites_id; eassumption.
    (* [comment removed for export] *)
    step. br. zstep. step. step. if_cases K0; zify_cond K0.
    { (* [comment removed for export] *) exit4. }
    assert (PL2 : 7 + publen <= elen) by (revert K0; rewrite ?unsigned_lit by lia; lia). clear K0.
    set (ps := cur + 9 + publen) in *.
    destruct (nth_error bs (Z.to_nat (cur - Bb + (9 + publen)))) as [d0|] eqn:N0; [| apply nth_error_None in N0; lia]. pose proof (abyte_range d0) as D0R.
    destruct (nth_error bs (Z.to_nat (cur - Bb + (10 + publen)))) as [d1|] eqn:N1; [| apply nth_error_None in N1; lia]. pose proof (abyte_range d1) as D1R.
    pose proof (ade_byte _ _ _ _ _ _ BS N0 ltac:(lia) ltac:(lia)) as RD0. pose proof (ade_byte _ _ _ _ _ _ BS N1 ltac:(lia) ltac:(lia)) as RD1.
    replace (cur + (9 + publen)) with ps in RD0 by lia. replace (cur + (10 + publen)) with (ps + 1) in RD1 by lia.
    (* [comment removed for export] *)
    zstep. replace (cur + 9 + publen) with ps by lia.
    zstep. step. zstep. ck1_load ACCB ps v12 V1 V2 Hp12.
    ck_K 12 0x51ac3c K1.
    { intros tv1. red_tset.
      (* [comment removed for export] *)
      zstep. zstep. zstep. ck1_load ACCB (ps + 1) v13 W1 W2 Hp13.
      replace ps with (ps + 0) in RD0 by lia. step. change (zxb d0) with (Z_to_bv 64 (bv_unsigned d0)).
      ck_K 14 0x51ac54 K2.
      { intros tv2. red_tset.
        (* [comment removed for export] *)
        step. change (zxb d1) with (Z_to_bv 64 (bv_unsigned d1)). step.
        clear ACCB ACCE. st1. step.
        rewrite ?Z.shiftl_mul_pow2 by lia. rewrite ?(unsigned_lit (bv_unsigned d0)) by lia. rewrite ?(unsigned_lit (bv_unsigned d0 * 2 ^ 8)) by lia. rewrite ?(unsigned_lit (bv_unsigned d1)) by lia.
        rewrite (be16_lor (bv_unsigned d0) (bv_unsigned d1)) by lia.
        set (sl := bv_unsigned d1 + 256 * bv_unsigned d0) in *. assert (SLR : 0 <= sl < 2^16) by (subst sl; lia).
        zstep. st1.
        (* [comment removed for export] *)
        step. if_cases K0; zify_cond K0. { exit4. }
        assert (SLB : 7 + publen + sl <= elen) by (revert K0; rewrite ?unsigned_lit by lia; lia). clear K0.
        step. if_cases K0; zify_cond K0. { exit4. }
        assert (SL1 : 1 <= sl) by (revert K0; rewrite ?unsigned_lit by lia; lia). clear K0.
        step. zstep. step. step. if_cases K0; zify_cond K0. { exit4. }
        assert (EVEN : sl mod 2 = 0).
        { revert K0. rewrite ?unsigned_lit by lia. rewrite land_1. subst sl. clear - D0R D1R. intros K0. Z.div_mod_to_equations. lia. }
        clear K0.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
          assert (ACCE1 : accessible mx ee 104) by (unfold id in ACCE0; eapply accessible_across; [exact ACCE0| exact MU|];
            repeat (apply Forall_cons; [cbn; unfold AHI_LO, ALOWSH_LO in *; lia|]); apply Forall_nil) end.
        (* [comment removed for export] *)
        zstep. zstep. zstep. ck8_load ACCE1 (ee + 32). step. if_false_by (ck1_bnez_false 0 eq_refl).
        (* [comment removed for export] *)
        zstep. rewrite (Z.shiftr_div_pow2 sl 2) by lia. change (2 ^ 2) with 4.
        clear ACCE1. st1.
        (* [comment removed for export] *)
        step. step. step. step. step. step. step.
        apply evt_done. do 8 eexists. eexists. do 2 eexists. exists (sl / 4).
        repeat match goal with |- _ /\ _ => split end; try eassumption; [right; Z.div_mod_to_equations; lia|].
        right. exists sl. unfold bz. rewrite N0, N1.
        repeat match goal with |- _ /\ _ => split end; try reflexivity; try lia.
        all: first [unfold wz; f_equal; lia | subst ps; reflexivity | match goal with |- ?G => idtac "LEFT4:" G end]. }
      ck1_branch_bge (ps + 1) v13 W1 W2 Hp13 K2. }
    ck1_branch_bge ps v12 V1 V2 Hp12 K1.
    Unshelve. all: try exact (Z_to_bv 64 0); try exact 0.
  Qed.

  (* [comment removed for export] *)
  Lemma ade_seg5 :
    forall (rax gp tp t0 t1 t2 s0w a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (q SH cur publen b7 b8 b5 b6 sl ns ps ee SA : Z) (E : entrep) pad1 pad2 pad3 pad4
           (w16 w24 w32 w40 w48 w72 w96 w104 w112 w120 w128 : word),
      rw_cells asegs m (q + 16) (arp_sg1 w16 w24 w32 w40 w48 (wz b6) (wz b5) w72 (wz AECH_VERSION) (wz ADE_FILE) w96 w104 w112 w120 w128 (wz cur)) ->
      0 <= b5 < 256 -> 0 <= b6 < 256 -> 0 <= b7 < 256 -> 0 <= b8 < 256 -> publen = 256 * b7 + b8 -> 0 <= ns < 2^14 -> 0 <= SA -> SA + 6 * ns < 2^64 ->
      0 <= ps -> ps + 2 + sl < 2^64 -> 0 <= cur ->
      rw_cells asegs m ee (entry_cells E pad1 pad2 pad3 pad4) -> 0 < ee -> ee + ENTRY_SIZE <= aceil -> accessible m ee ENTRY_SIZE ->
      aceil <= q -> q + 312 < 2^64 -> mem_inv asegs m ->
      evt asegs (fun ms' => exists m1,
          munch [(ee + 40, ee + 48)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
          /\ rw_cells asegs m1 ee (entry_cells (upd_suites E SA (en_suites_o E)) pad1 pad2 pad3 pad4) /\
         (  (SA = 0 /\
             ms' = MS (mkR rax (Z_to_bv 64 q) gp tp t0 t1 t2 s0w (Z_to_bv 64 q) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 (ee + 40)) (Z_to_bv 64 0) a4 a5 (Z_to_bv 64 cur) a7
                           (Z_to_bv 64 ee) (Z_to_bv 64 SH) (Z_to_bv 64 b8) (Z_to_bv 64 sl) (Z_to_bv 64 (Z.shiftr (ee + 32) 3 + ASHB)) (Z_to_bv 64 ASHB)
                           (Z_to_bv 64 (256 * b7)) (Z_to_bv 64 ps) (Z_to_bv 64 (ee + 32)) (Z_to_bv 64 ns) t3 t4 t5 t6)
                      F (Z_to_bv 64 ADE_TZ) fc None m1 (seg_rom asegs))
         \/ (0 < SA /\
             ms' = MS (mkR rax (Z_to_bv 64 q) gp tp t0 t1 t2 s0w (Z_to_bv 64 q)
                           (Z_to_bv 64 (ps + 2 + sl)) (Z_to_bv 64 (SA + 6 * 0)) (Z_to_bv 64 (ee + 40)) (Z_to_bv 64 (4 * 0)) (Z_to_bv 64 (SA + 4 + 6 * 0))
                           (Z_to_bv 64 (256 * b5 + b6)) (Z_to_bv 64 (cur + publen)) (Z_to_bv 64 (0 - 1))
                           (Z_to_bv 64 ee) (Z_to_bv 64 SH) (Z_to_bv 64 b8) (Z_to_bv 64 sl) (Z_to_bv 64 (Z.shiftr (ee + 32) 3 + ASHB)) (Z_to_bv 64 ASHB)
                           (Z_to_bv 64 (256 * b7)) (Z_to_bv 64 (ps + 2)) (Z_to_bv 64 (ee + 32)) (Z_to_bv 64 (4 * ns)) t3 t4 t5 t6)
                      F (Z_to_bv 64 ADE_LH) fc None m1 (seg_rom asegs))))
        (MS (mkR rax (Z_to_bv 64 q) gp tp t0 t1 t2 s0w (Z_to_bv 64 q) (Z_to_bv 64 SA) a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 ee) (Z_to_bv 64 SH) (Z_to_bv 64 b8) (Z_to_bv 64 sl) (Z_to_bv 64 (Z.shiftr (ee + 32) 3 + ASHB)) (Z_to_bv 64 ASHB)
                 (Z_to_bv 64 (256 * b7)) (Z_to_bv 64 ps) (Z_to_bv 64 (ee + 32)) (Z_to_bv 64 ns) t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 ADE_R3)) fc None m (seg_rom asegs)).
  Proof.
    intros until w128. intros FA B5R B6R B7R B8R PLE NSR SA0 SAH PS0 PSH C0 EC EEP EEH ACCE CQ QH MI.
    unfold ADE_R3, ADE_TZ, ADE_LH in *. unfold arp_sg1, AECH_VERSION, ADE_FILE, ASHB, wz in FA |- *.
    unfold entry_cells in EC |- *. unfold ENTRY_SIZE in EEH, ACCE. retpc.
    acb. pose proof ACCE as (_ & AHIE & _). unfold AAPP_HI in AHIE.
    pose proof (munch_refl [(ee + 40, ee + 48)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    (* [comment removed for export] *)
    zstep. zstep. zstep. ck8_load ACCE (ee + 40). step. if_false_by (ck1_bnez_false 0 eq_refl).
    step. clear ACCE. st1. step. step. if_cases K0; zify_cond K0.
    { (* [comment removed for export] *)
      assert (SZ : SA = 0) by (revert K0; rewrite ?unsigned_lit by lia; lia). clear K0. subst SA.
      apply evt_done. eexists. repeat match goal with |- _ /\ _ => split end; try eassumption.
      left. split; [reflexivity| reflexivity]. }
    assert (SP : 0 < SA) by (revert K0; rewrite ?unsigned_lit by lia; lia). clear K0.
    (* [comment removed for export] *)
    step. step. step. zstep. zstep. step. zstep. step. step. zstep. zstep. step.
    rewrite ?Z.shiftl_mul_pow2 by lia. rewrite ?(unsigned_lit b5) by lia. rewrite ?(unsigned_lit (b5 * 2 ^ 8)) by lia. rewrite ?(unsigned_lit b6) by lia.
    rewrite ?land_W64. rewrite ?(Z.mod_small (b5 * 2 ^ 8) (2 ^ 64)) by lia.
    rewrite (be16_lor b5 b6) by lia.
    rewrite ?(unsigned_lit ns) by lia. rewrite ?(unsigned_lit (ns * 2 ^ 2)) by lia.
    apply evt_done. eexists. repeat match goal with |- _ /\ _ => split end; try eassumption.
    right. split; [exact SP|].
    replace (SA + 6 * 0) with SA by lia. replace (4 * 0) with 0 by lia. replace (SA + 4 + 6 * 0) with (SA + 4) by lia.
    replace (256 * b5 + b6) with (b6 + 256 * b5) by lia. replace (cur + publen) with (cur + 256 * b7 + b8) by lia. replace (4 * ns) with (ns * 2 ^ 2) by lia.
    change (0 - 1) with (-1).
    match goal with |- ?G => first [reflexivity | idtac "ST5:" G] end.
  Qed.

  (* [comment removed for export] *)
  Lemma ade_loop : forall (k : nat) (i : Z) (rax gp tp t0 t1 t2 s0w a2 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (q SH Bb blen src sl ns kem SA ee b8 h7 : Z) (bs : list byte) (E : entrep) pad1 pad2 pad3 pad4 junk,
      Z.of_nat k = ns - i -> 0 <= i <= ns -> en_nsuites E = ns -> 0 <= ns < 2^14 -> 4 * ns <= sl -> 0 <= kem < 2^16 -> 0 <= b8 < 2^64 -> 0 <= h7 < 2^64 ->
      rw_cells asegs m (q + 216) [C8 (wz ASHB)] ->
      rw_cells asegs m (SA + 6 * i) [CB (Z.to_nat (6 * (ns - i))) junk] -> 0 < SA -> SA + 6 * ns <= aceil -> accessible m SA (6 * ns) -> (SA + 6 * ns <= ALOWSH_LO \/ AHI_LO <= SA) ->
      bytes_at asegs m Bb bs -> 0 < Bb -> Bb + 11 <= src -> src + sl <= Bb + zlength bs -> Bb + zlength bs <= aceil -> accessible m Bb blen -> zlength bs <= blen ->
      (SA + 6 * ns <= Bb \/ Bb + zlength bs <= SA) ->
      rw_cells asegs m ee (entry_cells E pad1 pad2 pad3 pad4) -> 0 < ee -> ee + ENTRY_SIZE <= aceil -> accessible m ee ENTRY_SIZE -> (SA + 6 * ns <= ee \/ ee + ENTRY_SIZE <= SA) ->
      aceil <= q -> q + 312 < 2^64 -> mem_inv asegs m ->
      evt asegs (fun ms' => exists (a2' t0' t1' t2' t3' t4' t5' t6' : word) m1 junk',
          munch [(SA + 6 * i, SA + 6 * ns)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
          /\ rw_cells asegs m1 (SA + 6 * i) (asuite_cells (srows bs (Z.to_nat (src - Bb + 4 * i)) kem k) ++ [CB 0 junk'])
          /\ ms' = MS (mkR rax (Z_to_bv 64 q) gp tp t0' t1' t2' s0w (Z_to_bv 64 q)
                        (Z_to_bv 64 (src + sl)) (Z_to_bv 64 (SA + 6 * ns)) a2' (Z_to_bv 64 (4 * ns)) (Z_to_bv 64 (SA + 4 + 6 * ns))
                        (Z_to_bv 64 kem) (Z_to_bv 64 (src - 11)) (Z_to_bv 64 (ns - 1))
                        (Z_to_bv 64 ee) (Z_to_bv 64 SH) (Z_to_bv 64 b8) (Z_to_bv 64 sl) (Z_to_bv 64 (Z.shiftr (ee + 32) 3 + ASHB)) (Z_to_bv 64 ASHB)
                        (Z_to_bv 64 h7) (Z_to_bv 64 src) (Z_to_bv 64 (ee + 32)) (Z_to_bv 64 (4 * ns)) t3' t4' t5' t6')
                   F (Z_to_bv 64 ADE_J2) fc None m1 (seg_rom asegs))
        (MS (mkR rax (Z_to_bv 64 q) gp tp t0 t1 t2 s0w (Z_to_bv 64 q)
                 (Z_to_bv 64 (src + sl)) (Z_to_bv 64 (SA + 6 * i)) a2 (Z_to_bv 64 (4 * i)) (Z_to_bv 64 (SA + 4 + 6 * i))
                 (Z_to_bv 64 kem) (Z_to_bv 64 (src - 11)) (Z_to_bv 64 (i - 1))
                 (Z_to_bv 64 ee) (Z_to_bv 64 SH) (Z_to_bv 64 b8) (Z_to_bv 64 sl) (Z_to_bv 64 (Z.shiftr (ee + 32) 3 + ASHB)) (Z_to_bv 64 ASHB)
                 (Z_to_bv 64 h7) (Z_to_bv 64 src) (Z_to_bv 64 (ee + 32)) (Z_to_bv 64 (4 * ns)) t3 t4 t5 t6)
            F (Z_to_bv 64 ADE_LH) fc None m (seg_rom asegs)).
  Proof.
    induction k as [|k IH]; intros until junk; intros HK IR NSQ NSR SL4 KR B8R H7R F216 SC SAP SAH ACCS NSS BS BP SRC SRE BH ACCB BL SBA EC EEP EEH ACCE SEA CQ QH MI.
    - (* [comment removed for export] *)
      unfold ADE_LH, ADE_J2, ASHB in *. acb. pose proof (bytes_at_bound _ _ _ _ BS) as BB. unfold zlength in *.
      assert (IE : i = ns) by lia. subst i.
      pose proof (munch_refl [(SA + 6 * ns, SA + 6 * ns)] m) as MU. pose proof (wmono_refl asegs m) as WM.
      step. if_cases K0; zify_cond K0. 2: { exfalso. revert K0. rewrite ?unsigned_lit by lia. intros K0. apply K0. reflexivity. }
      apply evt_done. exists a2, t0, t1, t2, t3, t4, t5, t6, m, junk.
      repeat match goal with |- _ /\ _ => split end; try assumption. cbn [srows asuite_cells app]. rewrite Z.sub_diag in SC. exact SC. reflexivity.
    - (* [comment removed for export] *)
      unfold ADE_LH, ADE_J2, ASHB in *. unfold wz in F216. acb. pose proof (bytes_at_bound _ _ _ _ BS) as BB. unfold zlength in *. unfold entry_cells in EC. unfold ENTRY_SIZE in *.
      unfold ALOWSH_LO, AHI_LO in NSS. pose proof aceil_range as ACR.
      pose proof ACCB as (_ & AHIB & _). pose proof ACCE as (_ & AHIE & _). pose proof ACCS as (_ & AHIS & _). unfold AAPP_HI in AHIB, AHIE, AHIS.
      assert (IL : i < ns) by lia.
      pose proof (munch_refl [(SA + 6 * i, SA + 6 * ns)] m) as MU. pose proof (wmono_refl asegs m) as WM.
      pose proof ACCS as ACCS0. change (accessible m SA (6 * ns)) with (id (accessible m SA (6 * ns))) in ACCS0.
      pose proof ACCE as ACCE0. change (accessible m ee 104) with (id (accessible m ee 104)) in ACCE0.
      pose proof ACCB as ACCB0. change (accessible m Bb blen) with (id (accessible m Bb blen)) in ACCB0.
      Local Ltac reaccS ACCX0 MU N := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
        assert (N : accessible mx _ _) by (unfold id in ACCX0; eapply accessible_across; [exact ACCX0| exact MU|];
          repeat (apply Forall_cons; [cbn; unfold AHI_LO, ALOWSH_LO in *; lia|]); apply Forall_nil) end.
      (* [comment removed for export] *)
      step. if_cases K0; zify_cond K0. { exfalso. revert K0. rewrite ?unsigned_lit by lia. clear - IL IR NSR. lia. } clear K0.
      destruct (nth_error bs (Z.to_nat (src - Bb + 4 * i + 0))) as [e0|] eqn:M0; [| apply nth_error_None in M0; lia].
      destruct (nth_error bs (Z.to_nat (src - Bb + 4 * i + 1))) as [e1|] eqn:M1; [| apply nth_error_None in M1; lia].
      destruct (nth_error bs (Z.to_nat (src - Bb + 4 * i + 2))) as [e2|] eqn:M2; [| apply nth_error_None in M2; lia].
      destruct (nth_error bs (Z.to_nat (src - Bb + 4 * i + 3))) as [e3|] eqn:M3; [| apply nth_error_None in M3; lia].
      pose proof (ade_byte m Bb bs (src + 4 * i) 0 e0 BS ltac:(replace (src + 4 * i - Bb + 0) with (src - Bb + 4 * i + 0) by lia; exact M0) ltac:(lia) ltac:(lia)) as RD0.
      pose proof (ade_byte m Bb bs (src + 4 * i) 1 e1 BS ltac:(replace (src + 4 * i - Bb + 1) with (src - Bb + 4 * i + 1) by lia; exact M1) ltac:(lia) ltac:(lia)) as RD1.
      pose proof (ade_byte m Bb bs (src + 4 * i) 2 e2 BS ltac:(replace (src + 4 * i - Bb + 2) with (src - Bb + 4 * i + 2) by lia; exact M2) ltac:(lia) ltac:(lia)) as RD2.
      pose proof (ade_byte m Bb bs (src + 4 * i) 3 e3 BS ltac:(replace (src + 4 * i - Bb + 3) with (src - Bb + 4 * i + 3) by lia; exact M3) ltac:(lia) ltac:(lia)) as RD3.
      pose proof (abyte_range e0) as E0R. pose proof (abyte_range e1) as E1R. pose proof (abyte_range e2) as E2R. pose proof (abyte_range e3) as E3R.
      (* [comment removed for export] *)
      zstep. zstep. replace (src - 11 + 4 * i + 11) with (src + 4 * i) by lia.
      zstep. step. zstep. ck1_load ACCB (src + 4 * i) v16 V1 V2 H16.
      ck_K 7 0x51ad30 K1.
      { intros tv1. red_tset.
        (* [comment removed for export] *)
        zstep. zstep. replace (src - 11 + 4 * i + 12) with (src + 4 * i + 1) by lia.
        zstep. zstep. ck1_load ACCB (src + 4 * i + 1) v17 W1 W2 H17.
        step. change (zxb e0) with (Z_to_bv 64 (bv_unsigned e0)).
        ck_K 29 0x51ad4c K2.
        { intros tv2. red_tset.
          (* [comment removed for export] *)
          zstep. replace (src - 11 + 4 * i + 13) with (src + 4 * i + 2) by lia.
          zstep. zstep. ck1_load ACCB (src + 4 * i + 2) v18 X1 X2 H18.
          step. change (zxb e1) with (Z_to_bv 64 (bv_unsigned e1)).
          ck_K 30 0x51ad64 K3.
          { intros tv3. red_tset.
            (* [comment removed for export] *)
            zstep. replace (src - 11 + 4 * i + 14) with (src + 4 * i + 3) by lia.
            zstep. zstep. ck1_load ACCB (src + 4 * i + 3) v19 Y1 Y2 H19.
            step. change (zxb e2) with (Z_to_bv 64 (bv_unsigned e2)).
            ck_K 30 0x51ad7c K4.
            { intros tv4. red_tset.
              (* [comment removed for export] *)
              zstep. zstep. ck2_load ACCS (SA + 6 * i) v20 Z1 Z2 H20.
              step. change (zxb e3) with (Z_to_bv 64 (bv_unsigned e3)).
              ck_K 29 0x51ad90 K5.
              { intros tv5. red_tset.
                (* [comment removed for export] *)
                replace (SA + 4 + 6 * i) with (SA + 6 * i + 4) by lia.
                match goal with SCx : rw_cells asegs ?mx (SA + 6 * i) [CB _ junk] |- _ =>
                  pose proof (rw_cells_split_CB asegs mx (SA + 6 * i) [] (Z.to_nat (6 * (ns - i))) junk [] [6%nat; Z.to_nat (6 * (ns - (i + 1)))] SCx ltac:(cbn [sum_nat]; lia)) as SC2;
                  clear SCx; cbn [mk_CB_cells app] in SC2 end.
                set (Q := SA + 6 * i) in *.
                clear ACCB ACCS ACCE. st1.
                reaccS ACCS0 MU ACCS1.
                (* [comment removed for export] *)
                zstep. zstep. zstep. ck2_load ACCS1 (Q + 2) v21 U1 U2 H21.
                ck_K 30 0x51ada8 K6.
                { intros tv6. red_tset.
                  (* [comment removed for export] *)
                  step. step.
                  rewrite ?Z.shiftl_mul_pow2 by lia. rewrite ?(unsigned_lit (bv_unsigned e0)) by lia. rewrite ?land_W64. rewrite ?(Z.mod_small (bv_unsigned e0 * 2 ^ 8) (2 ^ 64)) by lia.
                  rewrite ?(unsigned_lit (bv_unsigned e0 * 2 ^ 8)) by lia. rewrite ?(unsigned_lit (bv_unsigned e1)) by lia.
                  rewrite (be16_lor (bv_unsigned e0) (bv_unsigned e1)) by lia.
                  zstep. clear ACCS1. st1.
                  reaccS ACCS0 MU ACCS2.
                  (* [comment removed for export] *)
                  zstep. zstep. ck2_load ACCS2 (Q + 4) v22 T1 T2 H22.
                  ck_K 7 0x51adc8 K7.
                  { intros tv7. red_tset.
                    (* [comment removed for export] *)
                    step. step.
                    rewrite ?Z.shiftl_mul_pow2 by lia. rewrite ?(unsigned_lit (bv_unsigned e2)) by lia. rewrite ?land_W64. rewrite ?(Z.mod_small (bv_unsigned e2 * 2 ^ 8) (2 ^ 64)) by lia.
                    rewrite ?(unsigned_lit (bv_unsigned e2 * 2 ^ 8)) by lia. rewrite ?(unsigned_lit (bv_unsigned e3)) by lia.
                    rewrite (be16_lor (bv_unsigned e2) (bv_unsigned e3)) by lia.
                    clear ACCS2. st1.
                    reaccS ACCE0 MU ACCE3.
                    (* [comment removed for export] *)
                    ck8_load ACCE3 (ee + 32). step. if_false_by (ck1_bnez_false 0 eq_refl).
                    step. rewrite NSQ. unfold zx32. rewrite wz_unsigned by lia. rewrite (Z.mod_small ns) by lia.
                    zstep. replace (i - 1 + 1) with i by lia. zstep. zstep. zstep.
                    step. if_cases K0; zify_cond K0; [| exfalso; revert K0; rewrite ?unsigned_lit by lia; clear - IL IR NSR; lia]. clear K0.
                    subst Q.
                    replace (SA + 6 * i + 6) with (SA + 6 * (i + 1)) by lia. replace (4 * i + 4) with (4 * (i + 1)) by lia. replace (SA + 6 * i + 10) with (SA + 4 + 6 * (i + 1)) by lia.
                    replace (Z_to_bv 64 i) with (Z_to_bv 64 (i + 1 - 1)) by (f_equal; lia).
                    lazymatch goal with SCy : rw_cells asegs ?mx (SA + 6 * i) [C2 _; C2 _; C2 _; CB _ _] |- _ =>
                      pose proof (proj1 (rw_cells_app asegs mx (SA + 6 * i) [C2 (Z_to_bv 64 kem); C2 (Z_to_bv 64 (bv_unsigned e1 + 256 * bv_unsigned e0)); C2 (Z_to_bv 64 (bv_unsigned e3 + 256 * bv_unsigned e2))] _) SCy) as [SC3 SC4];
                      cbn [cells_size csize Nat.add] in SC4; replace (SA + 6 * i + Z.of_nat 6) with (SA + 6 * (i + 1)) in SC4 by lia end.
                    clear ACCE3.
                    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
                      assert (ACCSn : accessible mx SA (6 * ns)) by (unfold id in ACCS0; eapply accessible_across; [exact ACCS0| exact MU|]; repeat (apply Forall_cons; [cbn; unfold AHI_LO, ALOWSH_LO in *; lia|]); apply Forall_nil);
                      assert (ACCEn : accessible mx ee 104) by (unfold id in ACCE0; eapply accessible_across; [exact ACCE0| exact MU|]; repeat (apply Forall_cons; [cbn; unfold AHI_LO, ALOWSH_LO in *; lia|]); apply Forall_nil);
                      assert (ACCBn : accessible mx Bb blen) by (unfold id in ACCB0; eapply accessible_across; [exact ACCB0| exact MU|]; repeat (apply Forall_cons; [cbn; unfold AHI_LO, ALOWSH_LO in *; lia|]); apply Forall_nil) end.
                    eapply evt_mono.
                    { eapply (IH (i + 1)); try eassumption; try (unfold entry_cells; eassumption); try (unfold wz; eassumption); rewrite ?Nat2Z.inj_succ in HK; try (clear - HK IL IR; lia).
                      all: try (unfold ENTRY_SIZE; lia). all: try (unfold ALOWSH_LO, AHI_LO; lia). all: match goal with |- ?G => idtac "IHLEFT:" G end. }
                    cbv beta. intros ms' (a2' & u0 & u1 & u2 & u3 & u4 & u5 & u6 & m1 & junk' & MU1 & WM1 & MI1 & SC5 & ->).
                    exists a2', u0, u1, u2, u3, u4, u5, u6, m1, junk'. repeat match goal with |- _ /\ _ => split end; try assumption.
                    + eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MU1]. intros x Hx. cbn in Hx |- *. lia.
                    + eapply wmono_trans; [exact WM| exact WM1].
                    + cbn [srows asuite_cells app]. replace (Z.to_nat (src - Bb + 4 * (i + 1))) with (4 + Z.to_nat (src - Bb + 4 * i))%nat in SC5 by lia.
                      unfold bz. replace (Z.to_nat (src - Bb + 4 * i)) with (Z.to_nat (src - Bb + 4 * i + 0)) by lia. rewrite M0.
                      replace (S (Z.to_nat (src - Bb + 4 * i + 0))) with (Z.to_nat (src - Bb + 4 * i + 1)) by lia. rewrite M1.
                      replace (S (Z.to_nat (src - Bb + 4 * i + 1))) with (Z.to_nat (src - Bb + 4 * i + 2)) by lia. rewrite M2.
                      replace (S (Z.to_nat (src - Bb + 4 * i + 2))) with (Z.to_nat (src - Bb + 4 * i + 3)) by lia. rewrite M3.
                      apply (proj2 (rw_cells_app asegs m1 (SA + 6 * i) [C2 (wz kem); C2 (wz (256 * bv_unsigned e0 + bv_unsigned e1)); C2 (wz (256 * bv_unsigned e2 + bv_unsigned e3))] _)). split.
                      * eapply rw_cells_transport; [| exact MU1| exact WM1| cbn; lia]. unfold wz.
                        replace (256 * bv_unsigned e0 + bv_unsigned e1) with (bv_unsigned e1 + 256 * bv_unsigned e0) by lia.
                        replace (256 * bv_unsigned e2 + bv_unsigned e3) with (bv_unsigned e3 + 256 * bv_unsigned e2) by lia. exact SC3.
                      * cbn [cells_size csize Nat.add]. replace (SA + 6 * i + Z.of_nat 6) with (SA + 6 * (i + 1)) by lia. fold bz in SC5.
                        replace (S (S (S (S (Z.to_nat (src - Bb + 4 * i + 0)))))) with (4 + Z.to_nat (src - Bb + 4 * i))%nat by lia. exact SC5.
                    + reflexivity. }
                  ck2_branch_bge (Q + 4) v22 T1 T2 H22 K7. }
                ck2_branch_bge (Q + 2) v21 U1 U2 H21 K6. }
              ck2_branch_bge (SA + 6 * i) v20 Z1 Z2 H20 K5. }
            ck1_branch_bge (src + 4 * i + 3) v19 Y1 Y2 H19 K4. }
          ck1_branch_bge (src + 4 * i + 2) v18 X1 X2 H18 K3. }
        ck1_branch_bge (src + 4 * i + 1) v17 W1 W2 H17 K2. }
      ck1_branch_bge (src + 4 * i) v16 V1 V2 H16 K1.
      Unshelve. all: try exact (Z_to_bv 64 0); try exact 0; try exact [].
  Qed.

  (* [comment removed for export] *)
  Lemma ade_seg7 :
    forall (rax gp tp t0 t1 t2 s0w a2 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (q SH Bb blen src sl ns kem SA ee b8 h7 r48 d1 : Z) (bs : list byte) (E : entrep) pad1 pad2 pad3 pad4
           (w16 w24 w32 w40 w56 w64 w80 w88 w96 w104 w112 w128 w136 : word) (w152 w160 w168 w176 w184 w192 w200 w208 w224 w232 : word) (x0 x1 x2 n0 n1 n2 p0 p1 p2 : word),
      rw_cells asegs m (q + 16) (arp_sg1 w16 w24 w32 w40 (wz r48) w56 w64 (wz d1) w80 w88 w96 w104 w112 (wz Bb) w128 w136) ->
      rw_cells asegs m (q + 144) (arp_sg2 (wz ee) w152 w160 w168 w176 w184 w192 w200 w208 (wz ASHB) w224 w232) ->
      rw_cells asegs m (q + 240) (arp_sg3 x0 x1 x2 n0 n1 n2 p0 p1 p2) ->
      bytes_at asegs m Bb bs -> 0 < Bb -> Bb + 11 <= src -> 0 <= sl <= r48 -> src + r48 <= Bb + zlength bs -> Bb + zlength bs <= aceil -> accessible m Bb blen -> zlength bs <= blen ->
      0 <= d1 < 256 -> 0 <= ns -> 0 <= SA -> SA + 4 + 6 * ns < 2^64 -> 0 <= kem < 2^16 -> 0 <= b8 < 2^64 -> 0 <= h7 < 2^64 ->
      rw_cells asegs m ee (entry_cells E pad1 pad2 pad3 pad4) -> 0 < ee -> ee + ENTRY_SIZE <= aceil -> (Bb + zlength bs <= ee \/ ee + ENTRY_SIZE <= Bb) ->
      accessible m ee ENTRY_SIZE -> (ee + ENTRY_SIZE <= ALOWSH_LO \/ AHI_LO <= ee) ->
      aceil <= q -> q + 312 < 2^64 -> mem_inv asegs m ->
      evt asegs (fun ms' => exists (a0' a1' a2' a3' s4' s9' s10' : word) m1 (n0' n1' n2' : word) (mx : Z) (line : Z),
          munch [(ee + 48, ee + 49); (q + 264, q + 288)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
          /\ rw_cells asegs m1 (q + 240) (arp_sg3 x0 x1 x2 n0' n1' n2' p0 p1 p2)
          /\ rw_cells asegs m1 ee (entry_cells (upd_maxname E mx) pad1 pad2 pad3 pad4) /\ (mx = en_maxname E \/ 0 <= mx < 256) /\
         (  ((line = 420 \/ line = 425) /\
             ms' = MS (mkR rax (Z_to_bv 64 q) gp tp t0 t1 t2 s0w (Z_to_bv 64 q) a0' a1' a2' a3' (Z_to_bv 64 (SA + 4 + 6 * ns)) (Z_to_bv 64 kem) (Z_to_bv 64 (src - 11)) (Z_to_bv 64 (ns - 1))
                           (Z_to_bv 64 ee) (Z_to_bv 64 SH) s4' (Z_to_bv 64 sl) (Z_to_bv 64 (Z.shiftr (ee + 32) 3 + ASHB)) (Z_to_bv 64 ASHB)
                           (Z_to_bv 64 h7) s9' s10' (Z_to_bv 64 line) t3 t4 t5 t6)
                      F (Z_to_bv 64 ADE_TA) fc None m1 (seg_rom asegs))
         \/ (exists nl, sl + 2 <= r48 /\ nl = bz bs (Z.to_nat (src - Bb + sl + 1)) /\ sl + 2 + nl <= r48 /\ mx = bz bs (Z.to_nat (src - Bb + sl)) /\
             n0' = wz (src + sl + 2) /\ n1' = wz Bb /\ n2' = wz nl /\ line = 425 /\
             ms' = MS (mkR (Z_to_bv 64 ADE_R4) (Z_to_bv 64 q) gp tp t0 t1 t2 s0w (Z_to_bv 64 q)
                           (Z_to_bv 64 (src + sl + 2)) (Z_to_bv 64 0) (Z_to_bv 64 nl) a3' (Z_to_bv 64 (SA + 4 + 6 * ns)) (Z_to_bv 64 kem) (Z_to_bv 64 (src - 11)) (Z_to_bv 64 (ns - 1))
                           (Z_to_bv 64 ee) (Z_to_bv 64 SH) (Z_to_bv 64 (r48 - sl - 2)) (Z_to_bv 64 sl) (Z_to_bv 64 (Z.shiftr (ee + 32) 3 + ASHB)) (Z_to_bv 64 ASHB)
                           (Z_to_bv 64 h7) (Z_to_bv 64 nl) (Z_to_bv 64 (src + sl + 2)) (Z_to_bv 64 425) t3 t4 t5 t6)
                      F (Z_to_bv 64 P_memchr) fc None m1 (seg_rom asegs))))
        (MS (mkR rax (Z_to_bv 64 q) gp tp t0 t1 t2 s0w (Z_to_bv 64 q)
                 (Z_to_bv 64 (src + sl)) (Z_to_bv 64 (SA + 6 * ns)) a2 (Z_to_bv 64 (4 * ns)) (Z_to_bv 64 (SA + 4 + 6 * ns)) (Z_to_bv 64 kem) (Z_to_bv 64 (src - 11)) (Z_to_bv 64 (ns - 1))
                 (Z_to_bv 64 ee) (Z_to_bv 64 SH) (Z_to_bv 64 b8) (Z_to_bv 64 sl) (Z_to_bv 64 (Z.shiftr (ee + 32) 3 + ASHB)) (Z_to_bv 64 ASHB)
                 (Z_to_bv 64 h7) (Z_to_bv 64 src) (Z_to_bv 64 (ee + 32)) (Z_to_bv 64 (4 * ns)) t3 t4 t5 t6)
            F (Z_to_bv 64 ADE_J2) fc None m (seg_rom asegs)).
  Proof.
    intros until p2. intros FA FB FC BS BP SRC SLR SRE BH ACCB BL D1R NS0 SA0 SAH KR B8R H7R EC EEP EEH EBA ACCE NSE CQ QH MI.
    unfold ADE_J2, ADE_TA, ADE_R4, P_memchr in *. unfold arp_sg1, arp_sg2, arp_sg3, ASHB, wz in FA, FB, FC |- *.
    unfold entry_cells in EC |- *. unfold ENTRY_SIZE in EEH, EBA, ACCE, NSE. unfold ALOWSH_LO, AHI_LO in NSE. pose proof aceil_range as ACR.
    acb. pose proof (bytes_at_bound _ _ _ _ BS) as BB. unfold zlength in *.
    pose proof ACCB as (_ & AHIB & _). pose proof ACCE as (_ & AHIE & _). unfold AAPP_HI in AHIB, AHIE.
    pose proof (munch_refl [(ee + 48, ee + 49); (q + 264, q + 288)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof ACCB as ACCB0. change (accessible m Bb blen) with (id (accessible m Bb blen)) in ACCB0.
    pose proof ACCE as ACCE0. change (accessible m ee 104) with (id (accessible m ee 104)) in ACCE0.
    set (pe := src + sl) in *.
    Local Ltac exit7a := apply evt_done; do 7 eexists; eexists; do 3 eexists; eexists; eexists;
      repeat match goal with |- _ /\ _ => split end; [eassumption| eassumption| eassumption| eassumption| | | left; split; [| reflexivity]];
      [rewrite upd_maxname_id; eassumption| left; reflexivity| ].
    (* [comment removed for export] *)
    step. step. step. if_cases K0; zify_cond K0.
    { exit7a. left; reflexivity. }
    assert (SL1 : sl + 1 <= r48) by (revert K0; rewrite ?unsigned_lit by lia; lia). clear K0.
    (* [comment removed for export] *)
    step. zstep. step. step. if_cases K0; zify_cond K0.
    { exit7a. left; reflexivity. }
    clear K0.
    destruct (nth_error bs (Z.to_nat (src - Bb + sl))) as [g0|] eqn:G0; [| apply nth_error_None in G0; lia]. pose proof (abyte_range g0) as G0R.
    pose proof (ade_byte m Bb bs pe 0 g0 BS ltac:(replace (pe - Bb + 0) with (src - Bb + sl) by lia; exact G0) ltac:(lia) ltac:(lia)) as RD0.
    (* [comment removed for export] *)
    zstep. zstep. ck1_load ACCB pe v24 V1 V2 H24.
    ck_K 12 0x51aebc K1.
    { intros tv1. red_tset.
      (* [comment removed for export] *)
      step. zstep. zstep. step. zstep. ck8_load ACCE (ee + 48). step. change (zxb g0) with (Z_to_bv 64 (bv_unsigned g0)). step. if_false_by (ck1_bnez_false 0 eq_refl).
      (* [comment removed for export] *)
      step. step. step.
      rewrite ?(unsigned_lit sl) by lia. rewrite (add_not64 r48 sl) by lia.
      clear ACCB ACCE. st1. step. step. if_cases K0; zify_cond K0.
      { (* [comment removed for export] *)
        apply evt_done; do 7 eexists; eexists; do 3 eexists; eexists; eexists.
        repeat match goal with |- _ /\ _ => split end; [eassumption| eassumption| eassumption| eassumption| | | left; split; [right; reflexivity| reflexivity]].
        { lazymatch goal with H : rw_cells _ ?mx ?eex (C2 _ :: _) |- rw_cells _ _ ?eex _ => rewrite Z.mod_small in H by lia; exact H end. }
        right; lia. }
      assert (SL2 : sl + 2 <= r48) by (revert K0; rewrite ?unsigned_lit by lia; lia). clear K0.
      destruct (nth_error bs (Z.to_nat (src - Bb + sl + 1))) as [g1|] eqn:G1; [| apply nth_error_None in G1; lia]. pose proof (abyte_range g1) as G1R.
      lazymatch goal with BSx : bytes_at asegs ?mx Bb bs |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
        pose proof (ade_byte mx Bb bs pe 1 g1 BSx ltac:(replace (pe - Bb + 1) with (src - Bb + sl + 1) by lia; exact G1) ltac:(lia) ltac:(lia)) as RD1 end.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
        assert (ACCB1 : accessible mx Bb blen) by (unfold id in ACCB0; eapply accessible_across; [exact ACCB0| exact MU|]; repeat (apply Forall_cons; [cbn; unfold AHI_LO, ALOWSH_LO in *; lia|]); apply Forall_nil) end.
      (* [comment removed for export] *)
      zstep. zstep. step. zstep. ck1_load ACCB1 (pe + 1) v26 W1 W2 H26.
      ck_K 13 0x51af0c K2.
      { intros tv2. red_tset.
        (* [comment removed for export] *)
        step. change (zxb g1) with (Z_to_bv 64 (bv_unsigned g1)). zstep. step. if_cases K0; zify_cond K0.
        { (* [comment removed for export] *)
          apply evt_done; do 7 eexists; eexists; do 3 eexists; eexists; eexists.
          repeat match goal with |- _ /\ _ => split end; [eassumption| eassumption| eassumption| eassumption| | | left; split; [right; reflexivity| reflexivity]].
          { lazymatch goal with H : rw_cells _ ?mx ?eex (C2 _ :: _) |- rw_cells _ _ ?eex _ => rewrite Z.mod_small in H by lia; exact H end. }
          right; lia. }
        assert (NLB : sl + 2 + bv_unsigned g1 <= r48) by (revert K0; rewrite ?unsigned_lit by lia; lia). clear K0.
        (* [comment removed for export] *)
        zstep. clear ACCB1. st1. step. st1. st1. step. step. step. step. step.
        apply evt_done; do 7 eexists; eexists; do 3 eexists; eexists; eexists.
        repeat match goal with |- _ /\ _ => split end; [eassumption| eassumption| eassumption| eassumption| | |].
        { lazymatch goal with H : rw_cells _ ?mx ?eex (C2 _ :: _) |- rw_cells _ _ ?eex _ => rewrite Z.mod_small in H by lia; exact H end. }
        { right; lia. }
        right. exists (bv_unsigned g1). unfold bz. rewrite G0, G1.
        repeat match goal with |- _ /\ _ => split end; try reflexivity; try lia.
        subst pe. replace (r48 - sl - 1 + -1) with (r48 - sl - 2) by lia. reflexivity. }
      ck1_branch_bge (pe + 1) v26 W1 W2 H26 K2. }
    ck1_branch_bge pe v24 V1 V2 H24 K1.
    Unshelve. all: try exact (Z_to_bv 64 0); try exact 0.
  Qed.

  (* [comment removed for export] *)
  Lemma ade_seg8 :
    forall (rax gp tp t0 t1 t2 s0w a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s10 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (q nl mres ee : Z) (w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 : word),
      rw_cells asegs m (q + 144) (arp_sg2 (wz ee) w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232) ->
      0 <= nl < 256 -> 0 <= mres < 2^64 -> 0 <= ee -> ee + ENTRY_SIZE < 2^64 -> 0 <= q -> q + 312 < 2^64 -> mem_inv asegs m ->
      evt asegs (fun ms' =>
            ((nl < 4 \/ mres <> 0) /\
             ms' = MS (mkR rax (Z_to_bv 64 q) gp tp t0 t1 t2 s0w (Z_to_bv 64 q) (Z_to_bv 64 mres) (Z_to_bv 64 4) a2 a3 a4 a5 a6 a7
                           s2 s3 s4 s5 s6 s7 s8 (Z_to_bv 64 nl) s10 (Z_to_bv 64 431) t3 t4 t5 t6)
                      F (Z_to_bv 64 ADE_TA) fc None m (seg_rom asegs))
         \/ (4 <= nl /\ mres = 0 /\
             ms' = MS (mkR (Z_to_bv 64 ADE_R5) (Z_to_bv 64 q) gp tp t0 t1 t2 s0w (Z_to_bv 64 q) (Z_to_bv 64 (q + 264)) (Z_to_bv 64 (ee + 8)) a2 a3 a4 a5 a6 a7
                           s2 s3 s4 s5 s6 s7 s8 (Z_to_bv 64 nl) s10 (Z_to_bv 64 431) t3 t4 t5 t6)
                      F (Z_to_bv 64 P_PACKET_strndup) fc None m (seg_rom asegs)))
        (MS (mkR rax (Z_to_bv 64 q) gp tp t0 t1 t2 s0w (Z_to_bv 64 q) (Z_to_bv 64 mres) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 (Z_to_bv 64 nl) s10 (Z_to_bv 64 425) t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 ADE_R4)) fc None m (seg_rom asegs)).
  Proof.
    intros until w232. intros FB NLR MR EE0 EEH Q0 QH MI.
    unfold ADE_R4, ADE_R5, ADE_TA, P_PACKET_strndup in *. unfold arp_sg2, wz in FB. unfold ENTRY_SIZE in EEH. retpc.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
    (* [comment removed for export] *)
    step. step. step. if_cases K0; zify_cond K0.
    { apply evt_done. left. split; [left; revert K0; rewrite ?unsigned_lit by lia; lia| reflexivity]. }
    assert (NL4 : 4 <= nl) by (revert K0; rewrite ?unsigned_lit by lia; lia). clear K0.
    (* [comment removed for export] *)
    step. if_cases K0; zify_cond K0.
    { apply evt_done. left. split; [right; revert K0; rewrite ?unsigned_lit by lia; lia| reflexivity]. }
    assert (M0 : mres = 0) by (revert K0; rewrite ?unsigned_lit by lia; lia). clear K0. subst mres.
    (* [comment removed for export] *)
    step. zstep. zstep. step.
    apply evt_done. right. split; [exact NL4|]. split; [reflexivity|]. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma ade_seg9 :
    forall (rax gp tp t0 t1 t2 s0w a1 a2 a3 a4 a5 a6 a7 s2 s5 s6 s8 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (q SH Bb blen nm nl rleft rv ee : Z) (bs : list byte)
           (w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w128 w136 : word)
           (w152 w160 w168 w176 w184 w192 w200 w208 w224 w232 : word) (x0 x1 x2 n0 n1 n2 p0 p1 p2 : word),
      rw_cells asegs m (q + 16) (arp_sg1 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 (wz Bb) w128 w136) ->
      rw_cells asegs m (q + 144) (arp_sg2 (wz ee) w152 w160 w168 w176 w184 w192 w200 w208 (wz ASHB) w224 w232) ->
      rw_cells asegs m (q + 240) (arp_sg3 x0 x1 x2 n0 n1 n2 p0 p1 p2) ->
      bytes_at asegs m Bb bs -> 0 < Bb -> Bb <= nm -> 0 <= nl -> nl <= rleft -> nm + rleft <= Bb + zlength bs -> Bb + zlength bs <= aceil ->
      accessible m Bb blen -> zlength bs <= blen -> 0 <= rleft < 2^16 -> 0 <= rv <= 1 -> 0 <= ee -> ee + ENTRY_SIZE < 2^64 ->
      aceil <= q -> q + 312 < 2^64 -> mem_inv asegs m ->
      evt asegs (fun ms' => exists (a0' a1' a2' a3' a4' a5' s4' s5' : word) m1 (x0' x1' x2' : word) (line : Z),
          munch [(q + 240, q + 264)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
          /\ rw_cells asegs m1 (q + 240) (arp_sg3 x0' x1' x2' n0 n1 n2 p0 p1 p2) /\
         (  ((line = 431 \/ line = 442) /\
             ms' = MS (mkR rax (Z_to_bv 64 q) gp tp t0 t1 t2 s0w (Z_to_bv 64 q) a0' a1' a2' a3' a4' a5' a6 a7
                           s2 (Z_to_bv 64 SH) s4' s5' s6 (Z_to_bv 64 ASHB) s8 (Z_to_bv 64 nl) (Z_to_bv 64 nm) (Z_to_bv 64 line) t3 t4 t5 t6)
                      F (Z_to_bv 64 ADE_TA) fc None m1 (seg_rom asegs))
         \/ (exists xl, rv = 1 /\ nl + 2 <= rleft /\ xl = 256 * bz bs (Z.to_nat (nm - Bb + nl)) + bz bs (Z.to_nat (nm - Bb + nl + 1)) /\ nl + 2 + xl <= rleft /\
             x0' = wz (nm + nl + 2) /\ x1' = wz Bb /\ x2' = wz xl /\ line = 442 /\
             (  (xl = 0 /\
                 ms' = MS (mkR rax (Z_to_bv 64 q) gp tp t0 t1 t2 s0w (Z_to_bv 64 q) (Z_to_bv 64 Bb) a1' (Z_to_bv 64 (rleft - nl - 2)) a3' a4' a5' a6 a7
                               s2 (Z_to_bv 64 SH) (Z_to_bv 64 xl) (Z_to_bv 64 (nm + nl + 2)) s6 (Z_to_bv 64 ASHB) s8 (Z_to_bv 64 nl) (Z_to_bv 64 nm) (Z_to_bv 64 442) t3 t4 t5 t6)
                          F (Z_to_bv 64 ADE_J3) fc None m1 (seg_rom asegs))
             \/ (1 <= xl /\
                 ms' = MS (mkR (Z_to_bv 64 ADE_R6) (Z_to_bv 64 q) gp tp t0 t1 t2 s0w (Z_to_bv 64 q) (Z_to_bv 64 ee) (Z_to_bv 64 (q + 240)) (Z_to_bv 64 (rleft - nl - 2)) a3' a4' a5' a6 a7
                               s2 (Z_to_bv 64 SH) (Z_to_bv 64 xl) (Z_to_bv 64 (nm + nl + 2)) s6 (Z_to_bv 64 ASHB) s8 (Z_to_bv 64 nl) (Z_to_bv 64 nm) (Z_to_bv 64 442) t3 t4 t5 t6)
                          F (Z_to_bv 64 P_ech_decode_echconfig_exts) fc None m1 (seg_rom asegs))))))
        (MS (mkR rax (Z_to_bv 64 q) gp tp t0 t1 t2 s0w (Z_to_bv 64 q) (Z_to_bv 64 rv) a1 a2 a3 a4 a5 a6 a7
                 s2 (Z_to_bv 64 SH) (Z_to_bv 64 rleft) s5 s6 (Z_to_bv 64 ASHB) s8 (Z_to_bv 64 nl) (Z_to_bv 64 nm) (Z_to_bv 64 431) t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 ADE_R5)) fc None m (seg_rom asegs)).
  Proof.
    intros until p2. intros FA FB FC BS BP BNM NL0 NLR NMR BH ACCB BL RLR RVR EE0 EEH CQ QH MI.
    unfold ADE_R5, ADE_R6, ADE_TA, ADE_J3, P_ech_decode_echconfig_exts in *. unfold arp_sg1, arp_sg2, arp_sg3, ASHB, wz in FA, FB, FC |- *. unfold ENTRY_SIZE in EEH. retpc.
    acb. pose proof (bytes_at_bound _ _ _ _ BS) as BB. unfold zlength in *. pose proof aceil_range as ACR.
    pose proof ACCB as (_ & AHIB & _). unfold AAPP_HI in AHIB.
    pose proof (munch_refl [(q + 240, q + 264)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    Local Ltac exit9 L := apply evt_done; do 8 eexists; eexists; do 3 eexists; exists L;
      repeat match goal with |- _ /\ _ => split end; [eassumption| eassumption| eassumption| eassumption| left; split; [| reflexivity]].
    (* [comment removed for export] *)
    step. if_cases K0; zify_cond K0.
    { exit9 431. left; reflexivity. }
    assert (RV1 : rv = 1) by (revert K0; rewrite ?unsigned_lit by lia; lia). clear K0.
    (* [comment removed for export] *)
    zstep. step. step. step. if_cases K0; zify_cond K0.
    { exit9 442. right; reflexivity. }
    assert (NL2 : nl + 2 <= rleft) by (revert K0; rewrite ?unsigned_lit by lia; lia). clear K0.
    destruct (nth_error bs (Z.to_nat (nm - Bb + nl))) as [g0|] eqn:G0; [| apply nth_error_None in G0; lia]. pose proof (abyte_range g0) as G0R.
    destruct (nth_error bs (Z.to_nat (nm - Bb + nl + 1))) as [g1|] eqn:G1; [| apply nth_error_None in G1; lia]. pose proof (abyte_range g1) as G1R.
    pose proof (ade_byte m Bb bs (nm + nl) 0 g0 BS ltac:(replace (nm + nl - Bb + 0) with (nm - Bb + nl) by lia; exact G0) ltac:(lia) ltac:(lia)) as RD0.
    pose proof (ade_byte m Bb bs (nm + nl) 1 g1 BS ltac:(replace (nm + nl - Bb + 1) with (nm - Bb + nl + 1) by lia; exact G1) ltac:(lia) ltac:(lia)) as RD1.
    (* [comment removed for export] *)
    zstep. zstep. step. zstep. ck1_load ACCB (nm + nl) v27 V1 V2 H27.
    ck_K 13 0x51af8c K1.
    { intros tv1. red_tset.
      (* [comment removed for export] *)
      zstep. zstep. step. zstep. ck1_load ACCB (nm + nl + 1) v28 W1 W2 H28.
      step. change (zxb g0) with (Z_to_bv 64 (bv_unsigned g0)).
      ck_K 15 0x51afa8 K2.
      { intros tv2. red_tset.
        (* [comment removed for export] *)
        step. change (zxb g1) with (Z_to_bv 64 (bv_unsigned g1)). step. step.
        rewrite ?Z.shiftl_mul_pow2 by lia. rewrite ?(unsigned_lit (bv_unsigned g0)) by lia. rewrite ?land_W64. rewrite ?(Z.mod_small (bv_unsigned g0 * 2 ^ 8) (2 ^ 64)) by lia.
        rewrite ?(unsigned_lit (bv_unsigned g0 * 2 ^ 8)) by lia. rewrite ?(unsigned_lit (bv_unsigned g1)) by lia.
        rewrite (be16_lor (bv_unsigned g0) (bv_unsigned g1)) by lia.
        set (xl := bv_unsigned g1 + 256 * bv_unsigned g0) in *. assert (XLR : 0 <= xl < 2^16) by (subst xl; lia).
        zstep. step. if_cases K0; zify_cond K0.
        { exit9 442. right; reflexivity. }
        assert (XLB : nl + 2 + xl <= rleft) by (revert K0; rewrite ?unsigned_lit by lia; lia). clear K0.
        (* [comment removed for export] *)
        zstep. clear ACCB. st1. step. st1. st1. step. if_cases K0; zify_cond K0.
        - (* [comment removed for export] *)
          assert (X0 : xl = 0) by (revert K0; rewrite ?unsigned_lit by lia; lia). clear K0.
          apply evt_done; do 8 eexists; eexists; do 3 eexists; exists 442.
          repeat match goal with |- _ /\ _ => split end; [eassumption| eassumption| eassumption| eassumption|].
          right. exists xl. unfold bz. rewrite G0, G1. repeat match goal with |- _ /\ _ => split end; try reflexivity; try lia.
          left. split; [exact X0|]. replace (rleft - nl - 2) with (rleft - nl + -2) by lia. reflexivity.
        - assert (X1 : 1 <= xl) by (revert K0; rewrite ?unsigned_lit by lia; lia). clear K0.
          (* [comment removed for export] *)
          zstep. step. step.
          apply evt_done; do 8 eexists; eexists; do 3 eexists; exists 442.
          repeat match goal with |- _ /\ _ => split end; [eassumption| eassumption| eassumption| eassumption|].
          right. exists xl. unfold bz. rewrite G0, G1. repeat match goal with |- _ /\ _ => split end; try reflexivity; try lia.
          right. split; [exact X1|]. replace (rleft - nl - 2) with (rleft - nl + -2) by lia. reflexivity. }
      ck1_branch_bge (nm + nl + 1) v28 W1 W2 H28 K2. }
    ck1_branch_bge (nm + nl) v27 V1 V2 H27 K1.
    Unshelve. all: try exact (Z_to_bv 64 0); try exact 0.
  Qed.

  (* [comment removed for export] *)
  Lemma ade_seg10 :
    forall (rax gp tp t0 t1 t2 s0w a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (q rv : Z),
      0 <= rv <= 1 -> 0 <= q -> q + 312 < 2^64 -> mem_inv asegs m ->
      evt asegs (fun ms' =>
            (rv = 0 /\
             ms' = MS (mkR rax (Z_to_bv 64 q) gp tp t0 t1 t2 s0w (Z_to_bv 64 q) (Z_to_bv 64 rv) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 (Z_to_bv 64 447) t3 t4 t5 t6)
                      F (Z_to_bv 64 ADE_TA) fc None m (seg_rom asegs))
         \/ (rv = 1 /\
             ms' = MS (mkR rax (Z_to_bv 64 q) gp tp t0 t1 t2 s0w (Z_to_bv 64 q) (Z_to_bv 64 rv) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 (Z_to_bv 64 442) t3 t4 t5 t6)
                      F (Z_to_bv 64 ADE_J3) fc None m (seg_rom asegs)))
        (MS (mkR rax (Z_to_bv 64 q) gp tp t0 t1 t2 s0w (Z_to_bv 64 q) (Z_to_bv 64 rv) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 (Z_to_bv 64 442) t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 ADE_R6)) fc None m (seg_rom asegs)).
  Proof.
    intros until rv. intros RVR Q0 QH MI. unfold ADE_R6, ADE_TA, ADE_J3 in *. retpc.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
    step. if_cases K0; zify_cond K0.
    - assert (R0 : rv = 0) by (revert K0; rewrite ?unsigned_lit by lia; lia). clear K0. step. step. apply evt_done. left. split; [exact R0| reflexivity].
    - assert (R1 : rv = 1) by (revert K0; rewrite ?unsigned_lit by lia; lia). clear K0. apply evt_done. right. split; [exact R1| reflexivity].
  Qed.

  (* [comment removed for export] *)
  Lemma ade_seg11 :
    forall (rax gp tp t0 t1 t2 s0w a0 a1 a2 a3 a4 a5 a6 a7 s2 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (q SH cur xs xl ee : Z) (E : entrep) pad1 pad2 pad3 pad4
           (w16 w24 w32 w40 w48 w56 w64 w72 w80 w96 w104 w112 w120 w128 : word) (w152 w160 w168 w176 w184 w192 w200 w208 w224 w232 : word),
      rw_cells asegs m (q + 16) (arp_sg1 w16 w24 w32 w40 w48 w56 w64 w72 w80 (wz ADE_FILE) w96 w104 w112 w120 w128 (wz cur)) ->
      rw_cells asegs m (q + 144) (arp_sg2 (wz ee) w152 w160 w168 w176 w184 w192 w200 w208 (wz ASHB) w224 w232) ->
      0 <= cur <= xs -> 0 <= xl -> xs + xl < 2^64 ->
      rw_cells asegs m ee (entry_cells E pad1 pad2 pad3 pad4) -> 0 < ee -> ee + ENTRY_SIZE <= aceil -> accessible m ee ENTRY_SIZE ->
      aceil <= q -> q + 312 < 2^64 -> mem_inv asegs m ->
      evt asegs (fun ms' => exists m1,
          munch [(ee + 88, ee + 96)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
          /\ rw_cells asegs m1 ee (entry_cells (upd_enclen E (xs + xl - cur)) pad1 pad2 pad3 pad4)
          /\ ms' = MS (mkR (Z_to_bv 64 ADE_R7) (Z_to_bv 64 q) gp tp t0 t1 t2 s0w (Z_to_bv 64 q)
                        (Z_to_bv 64 cur) (Z_to_bv 64 (xs + xl - cur)) (Z_to_bv 64 ADE_FILE) (Z_to_bv 64 453) a4 a5 a6 a7
                        (Z_to_bv 64 ee) (Z_to_bv 64 SH) (Z_to_bv 64 (xs + xl)) (Z_to_bv 64 xs) s6 (Z_to_bv 64 ASHB) s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_CRYPTO_memdup) fc None m1 (seg_rom asegs))
        (MS (mkR rax (Z_to_bv 64 q) gp tp t0 t1 t2 s0w (Z_to_bv 64 q) a0 a1 a2 a3 a4 a5 a6 a7
                 s2 (Z_to_bv 64 SH) (Z_to_bv 64 xl) (Z_to_bv 64 xs) s6 (Z_to_bv 64 ASHB) s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 ADE_J3) fc None m (seg_rom asegs)).
  Proof.
    intros until w232. intros FA FB CX XL0 XH EC EEP EEH ACCE CQ QH MI.
    unfold ADE_J3, ADE_R7, ADE_FILE, P_CRYPTO_memdup in *. unfold arp_sg1, arp_sg2, ASHB, wz in FA, FB |- *.
    unfold entry_cells in EC |- *. unfold ENTRY_SIZE in EEH, ACCE.
    acb. pose proof ACCE as (_ & AHIE & _). unfold AAPP_HI in AHIE.
    pose proof (munch_refl [(ee + 88, ee + 96)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    (* [comment removed for export] *)
    step. zstep. zstep. step. zstep. ck8_load ACCE (ee + 88). step. if_false_by (ck1_bnez_false 0 eq_refl).
    (* [comment removed for export] *)
    zstep. step. zstep. step. clear ACCE. st1.
    (* [comment removed for export] *)
    step. step. step. step. step.
    apply evt_done. eexists. repeat match goal with |- _ /\ _ => split end; try eassumption.
    match goal with |- ?G => first [reflexivity | idtac "ST11:" G] end.
  Qed.

  (* [comment removed for export] *)
  Lemma ade_seg12 :
    forall (rax gp tp t0 t1 t2 s0w a1 a2 a3 a4 a5 a6 a7 s2x s3x s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (q D ee : Z) (E : entrep) pad1 pad2 pad3 pad4 (w152 w168 w176 w184 w192 w200 w208 w224 w232 : word),
      rw_cells asegs m (q + 144) (arp_sg2 (wz ee) w152 (wz 0) w168 w176 w184 w192 w200 w208 (wz ASHB) w224 w232) ->
      0 <= D < 2^64 ->
      rw_cells asegs m ee (entry_cells E pad1 pad2 pad3 pad4) -> 0 < ee -> ee + ENTRY_SIZE <= aceil -> accessible m ee ENTRY_SIZE ->
      aceil <= q -> q + 312 < 2^64 -> mem_inv asegs m ->
      evt asegs (fun ms' => exists m1,
          munch [(ee + 96, ee + 104)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
          /\ rw_cells asegs m1 ee (entry_cells (upd_encoded E D (en_encoded_o E)) pad1 pad2 pad3 pad4) /\
         (  (D = 0 /\
             ms' = MS (mkR rax (Z_to_bv 64 q) gp tp t0 t1 t2 s0w (Z_to_bv 64 q) (Z_to_bv 64 0) (Z_to_bv 64 (ee + 96)) (Z_to_bv 64 0) (Z_to_bv 64 ASHB) a4 a5 a6 a7
                           (Z_to_bv 64 ee) s3x s4 s5 s6 (Z_to_bv 64 ASHB) s8 s9 s10 s11 t3 t4 t5 t6)
                      F (Z_to_bv 64 ADE_TZ) fc None m1 (seg_rom asegs))
         \/ (0 < D /\
             ms' = MS (mkR (Z_to_bv 64 ADE_R8) (Z_to_bv 64 q) gp tp t0 t1 t2 s0w (Z_to_bv 64 q) (Z_to_bv 64 0) (Z_to_bv 64 (ee + 96)) (Z_to_bv 64 0) (Z_to_bv 64 ASHB) a4 a5 a6 a7
                           (Z_to_bv 64 ee) s3x s4 s5 s6 (Z_to_bv 64 ASHB) s8 s9 s10 s11 t3 t4 t5 t6)
                      F (Z_to_bv 64 P_time) fc None m1 (seg_rom asegs))))
        (MS (mkR rax (Z_to_bv 64 q) gp tp t0 t1 t2 s0w (Z_to_bv 64 q) (Z_to_bv 64 D) a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 ee) s3x s4 s5 s6 (Z_to_bv 64 ASHB) s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 ADE_R7)) fc None m (seg_rom asegs)).
  Proof.
    intros until w232. intros FB DR EC EEP EEH ACCE CQ QH MI.
    unfold ADE_R7, ADE_TZ, ADE_R8, P_time in *. unfold arp_sg2, ASHB, wz in FB |- *.
    unfold entry_cells in EC |- *. unfold ENTRY_SIZE in EEH, ACCE. retpc.
    acb. pose proof ACCE as (_ & AHIE & _). unfold AAPP_HI in AHIE.
    pose proof (munch_refl [(ee + 96, ee + 104)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    (* [comment removed for export] *)
    zstep. zstep. step. zstep. ck8_load ACCE (ee + 96). step. if_false_by (ck1_bnez_false 0 eq_refl).
    clear ACCE. st1. step. if_cases K0; zify_cond K0.
    { assert (D0 : D = 0) by (revert K0; rewrite ?unsigned_lit by lia; lia). clear K0. subst D.
      apply evt_done. eexists. repeat match goal with |- _ /\ _ => split end; try eassumption. left. split; [reflexivity| reflexivity]. }
    assert (DP : 0 < D) by (revert K0; rewrite ?unsigned_lit by lia; lia). clear K0.
    (* [comment removed for export] *)
    step. step. if_cases K0; zify_cond K0. 2: { exfalso. revert K0. rewrite ?unsigned_lit by lia. lia. } clear K0.
    step. step. step.
    apply evt_done. eexists. repeat match goal with |- _ /\ _ => split end; try eassumption. right. split; [exact DP|].
    match goal with |- ?G => first [reflexivity | idtac "ST12:" G] end.
  Qed.

  (* [comment removed for export] *)
  Lemma ade_seg13 :
    forall (rax gp tp t0 t1 t2 s0w a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (q SH ff tm ee : Z) (E : entrep) pad1 pad2 pad3 pad4 (w152 w160 w168 w184 w192 w200 w208 w224 w232 : word)
           (sa : list byte) (sb : byte) (sc sd se : list byte) (sr : byte) (sg : list byte),
      set_shadow_f8_stmt ->
      rw_cells asegs m (q + 144) (arp_sg2 (wz ee) w152 w160 w168 (wz (SH + 8)) w184 w192 w200 w208 (wz ASHB) w224 w232) ->
      rw_cells asegs m SH (arp_fshadow sa sb sc sd se sr sg) ->
      ASHB + AIMG_TOP / 8 <= SH -> SH + 512 < AHI_LO -> 0 <= tm < 2^64 ->
      rw_cells asegs m ee (entry_cells E pad1 pad2 pad3 pad4) -> 0 < ee -> ee + ENTRY_SIZE <= aceil -> accessible m ee ENTRY_SIZE -> aapp ee ENTRY_SIZE ->
      aceil <= q -> q + 312 < 2^64 -> mem_inv asegs m -> ACONST m ->
      evt asegs (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m1,
          ms' = MS (mkR (Z_to_bv 64 ADE_R10) (Z_to_bv 64 q) gp tp t0' t1' t2' s0w (Z_to_bv 64 q) (Z_to_bv 64 ee) a1' a2' a3' a4' a5' a6' a7'
                       s2 (Z_to_bv 64 SH) (Z_to_bv 64 ee) s5 s6 (Z_to_bv 64 ASHB) s8 s9 s10 s11 t3' t4' t5' t6')
                   F (Z_to_bv 64 P_ech_final_config_checks) fc None m1 (seg_rom asegs)
          /\ munch [(ee + 64, ee + 72); (SH + 4, SH + 5); (SH + 8, SH + 264)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
          /\ rw_cells asegs m1 ee (entry_cells (upd_loadtime E tm) pad1 pad2 pad3 pad4)
          /\ rw_cells asegs m1 SH (arp_fshadow sa (b8 0xf8) sc (poison_bytes 256 0xf8) se sr sg)
          /\ ACONST m1)
        (MS (mkR rax (Z_to_bv 64 q) gp tp t0 t1 t2 s0w (Z_to_bv 64 q) (Z_to_bv 64 tm) a1 a2 a3 a4 a5 a6 a7
                 s2 (Z_to_bv 64 SH) s4 s5 s6 (Z_to_bv 64 ASHB) s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 ADE_R8)) fc None m (seg_rom asegs)).
  Proof.
    intros until sg. intros SF8 FB FS SH1 SH2 TMR EC EEP EEH ACCE AAPE CQ QH MI AC. pose proof (aapp_not_shadowland _ _ AAPE) as NSE.
    unfold ADE_R8, ADE_R10, P_ech_final_config_checks in *. unfold arp_sg2, ASHB, wz in FB |- *. unfold arp_fshadow in FS |- *.
    unfold entry_cells in EC |- *. unfold ENTRY_SIZE in EEH, ACCE, NSE. unfold ALOWSH_LO, AHI_LO in NSE. retpc.
    unfold ASHB, AIMG_TOP in SH1. unfold AHI_LO in SH2. change (12386304 / 8) with 1548288 in SH1. pose proof aceil_range as ACR.
    acb. pose proof ACCE as (_ & AHIE & _). unfold AAPP_HI in AHIE.
    pose proof (munch_refl [(ee + 64, ee + 72); (SH + 4, SH + 5); (SH + 8, SH + 264)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    (* [comment removed for export] *)
    step. zstep. zstep. step. zstep. ck8_load ACCE (ee + 64). step. if_false_by (ck1_bnez_false 0 eq_refl).
    (* [comment removed for export] *)
    pose proof FS as FS0. change (id (rw_cells asegs m SH (arp_fshadow sa sb sc sd se sr sg))) in FS0. clear FS.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => pose proof (munch_refl [(ee + 64, ee + 72)] mx) as MUe; pose proof (wmono_refl asegs mx) as WMe end.
    step. clear ACCE. st1.
    unfold id, arp_fshadow in FS0. eapply rw_cells_transport in FS0; [| exact MUe| exact WMe| cbn; change (Z.of_nat 512) with 512; lia]. clear MUe WMe.
    step. step. step. step.
    (* [comment removed for export] *)
    lazymatch goal with FSx : rw_cells asegs ?mx SH (?c1 :: ?c2 :: ?c3 :: ?c4 :: ?rest) |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      pose proof FSx as SHC; change (rw_cells asegs mx SH ([c1; c2; c3] ++ (c4 :: rest))) in SHC; clear FSx end.
    apply (proj1 (rw_cells_app _ _ _ _ _)) in SHC. destruct SHC as [SH3 SHR4]. cbn [cells_size csize Nat.add] in SHR4. change (Z.of_nat 8) with 8 in SHR4.
    lazymatch type of SHR4 with rw_cells _ ?mx _ (?c4 :: ?rest) => change (rw_cells asegs mx (SH + 8) ([c4] ++ rest)) in SHR4 end.
    apply (proj1 (rw_cells_app _ _ _ _ _)) in SHR4. destruct SHR4 as [SH256 SHT]. cbn [cells_size csize Nat.add] in SHT. change (Z.of_nat 256) with 256 in SHT.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      assert (ACc : ACONST mc) by
        (eapply ACONST_frame; [exact AC| exact MU| exact WM|];
         apply Forall_cons; [eapply aconst_ok_aapp; [exact AAPE| cbn; lia| cbn; unfold ENTRY_SIZE; lia]|];
         apply Forall_cons; [apply aconst_ok_high; cbn [fst snd]; unfold sh, AIMG_TOP; rewrite ?ASHADOW_BASE_val; lia|];
         apply Forall_cons; [apply aconst_ok_high; cbn [fst snd]; unfold sh, AIMG_TOP; rewrite ?ASHADOW_BASE_val; lia| apply Forall_nil]) end.
    eapply evt_cut.
    { unfold set_shadow_f8_stmt, set_shadow_stmt in SF8. eapply SF8 with (n := 256); [reflexivity| reflexivity| lia| change (Z.to_nat 256) with 256%nat; exact SH256| assumption| exact ACc]. }
    cbv beta. intros ms1 PO. unfold set_shadow_post in PO.
    destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & mA & -> & MU1 & WM1 & MI1 & SH256').
    retpc. clear SH256. aland MU1 WM1.
    (* [comment removed for export] *)
    step. st1. step. step.
    finish.
    { (* [comment removed for export] *)
      lazymatch goal with |- rw_cells _ ?mx ?base _ =>
        lazymatch goal with A : rw_cells _ mx base [_; _; _], B : rw_cells _ mx (base + 8) [_], C : rw_cells _ mx (base + 8 + 256) _ |- _ =>
            change (Z.to_nat 256) with 256%nat in B;
            pose proof (proj2 (rw_cells_app asegs mx (base + 8) [CB 256 (poison_bytes 256 248)] _) (conj B ltac:(cbn [cells_size csize Nat.add]; change (Z.of_nat 256) with 256; exact C))) as BC;
            cbn [app] in BC;
            pose proof (proj2 (rw_cells_app asegs mx base _ _) (conj A ltac:(cbn [cells_size csize Nat.add]; change (Z.of_nat 8) with 8; exact BC))) as ABC;
            cbn [app] in ABC; first [exact ABC | match type of ABC with ?T => idtac "ABC:" T end; match goal with |- ?G => idtac "G:" G end] end end. }
    eapply ACONST_frame; [exact AC| exact MU| exact WM|].
    apply Forall_cons; [eapply aconst_ok_aapp; [exact AAPE| cbn; lia| cbn; unfold ENTRY_SIZE; lia]|].
    apply Forall_cons; [apply aconst_ok_high; cbn [fst snd]; unfold sh, AIMG_TOP; rewrite ?ASHADOW_BASE_val; lia|].
    apply Forall_cons; [apply aconst_ok_high; cbn [fst snd]; unfold sh, AIMG_TOP; rewrite ?ASHADOW_BASE_val; lia| apply Forall_nil].
  Qed.

  (* [comment removed for export] *)
  Lemma ade_seg14 :
    forall (rax gp tp t0 t1 t2 s0w a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (q frv ee es h lbuf btmp Bb ff z1 z2 : Z)
           (w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w112 w128 w136 : word) (w152 w160 w168 w176 w184 w224 w232 : word),
      rw_cells asegs m (q + 16) (arp_sg1 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 (wz lbuf) (wz btmp) w112 (wz Bb) w128 w136) ->
      rw_cells asegs m (q + 144) (arp_sg2 (wz ee) w152 w160 w168 w176 w184 (wz es) (wz ff) (wz ff) (wz ASHB) w224 w232) ->
      rw_cells asegs m es [C8 (wz h); C8 (wz z1); C8 (wz z2)] -> 0 < es -> es + STORE_SIZE <= aceil -> accessible m es STORE_SIZE ->
      0 <= frv <= 1 -> 0 <= h < 2^64 -> 0 <= ee < 2^64 -> 0 <= lbuf < 2^64 -> 0 <= btmp < 2^64 -> 0 <= Bb < 2^64 -> 0 <= ff < 2^64 ->
      aceil <= q -> q + 312 < 2^64 -> mem_inv asegs m ->
      evt asegs (fun ms' =>
            (frv = 0 /\
             ms' = MS (mkR rax (Z_to_bv 64 q) gp tp t0 t1 t2 s0w (Z_to_bv 64 q) (Z_to_bv 64 frv) a1 a2 a3 a4 a5 a6 a7
                           (Z_to_bv 64 ee) s3 s4 s5 (Z_to_bv 64 ff) (Z_to_bv 64 ff) (Z_to_bv 64 btmp) (Z_to_bv 64 Bb) (Z_to_bv 64 lbuf) s11 t3 t4 t5 t6)
                      F (Z_to_bv 64 ADE_TX2) fc None m (seg_rom asegs))
         \/ (frv = 1 /\ h <> 0 /\
             ms' = MS (mkR rax (Z_to_bv 64 q) gp tp t0 t1 t2 s0w (Z_to_bv 64 q) (Z_to_bv 64 h) a1 a2 a3 a4 a5 a6 a7
                           s2 s3 (Z_to_bv 64 (Z.shiftr es 3 + ASHB)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                      F (Z_to_bv 64 ADE_PUSH) fc None m (seg_rom asegs))
         \/ (frv = 1 /\ h = 0 /\
             ms' = MS (mkR (Z_to_bv 64 ADE_R11) (Z_to_bv 64 q) gp tp t0 t1 t2 s0w (Z_to_bv 64 q) (Z_to_bv 64 h) a1 a2 a3 a4 a5 a6 a7
                           s2 s3 (Z_to_bv 64 (Z.shiftr es 3 + ASHB)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                      F (Z_to_bv 64 P_OPENSSL_sk_new_null) fc None m (seg_rom asegs)))
        (MS (mkR rax (Z_to_bv 64 q) gp tp t0 t1 t2 s0w (Z_to_bv 64 q) (Z_to_bv 64 frv) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 ADE_R10)) fc None m (seg_rom asegs)).
  Proof.
    intros until w232. intros FA FB SC ESP ESH ACCS FRR HR EER LR BR BBR FFR CQ QH MI.
    unfold ADE_R10, ADE_TX2, ADE_PUSH, ADE_R11, P_OPENSSL_sk_new_null in *. unfold arp_sg1, arp_sg2, ASHB, wz in FA, FB, SC |- *. unfold STORE_SIZE in ESH, ACCS. retpc.
    acb. pose proof ACCS as (_ & AHIS & _). unfold AAPP_HI in AHIS.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
    (* [comment removed for export] *)
    step. if_cases K0; zify_cond K0.
    { (* [comment removed for export] *)
      assert (F0 : frv = 0) by (revert K0; rewrite ?unsigned_lit by lia; lia). clear K0.
      do 6 step. step.
      apply evt_done. left. split; [exact F0| reflexivity]. }
    assert (F1 : frv = 1) by (revert K0; rewrite ?unsigned_lit by lia; lia). clear K0.
    (* [comment removed for export] *)
    step. zstep. step. zstep. ck8_load ACCS es. step. if_false_by (ck1_bnez_false 0 eq_refl).
    step. step. step. if_cases K0; zify_cond K0.
    { assert (HNZ : h <> 0) by (revert K0; rewrite ?unsigned_lit by lia; lia). clear K0.
      apply evt_done. right; left. split; [exact F1|]. split; [exact HNZ| reflexivity]. }
    assert (HZ : h = 0) by (revert K0; rewrite ?unsigned_lit by lia; lia). clear K0.
    (* [comment removed for export] *)
    step. step. apply evt_done. right; right. split; [exact F1|]. split; [exact HZ| reflexivity].
  Qed.

  (* [comment removed for export] *)
  Lemma ade_seg15 :
    forall (rax gp tp t0 t1 t2 s0w a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (q sk : Z),
      0 <= sk < 2^64 -> 0 <= q -> q + 312 < 2^64 -> mem_inv asegs m ->
      evt asegs (fun ms' =>
          ms' = MS (mkR (Z_to_bv 64 ADE_R12) (Z_to_bv 64 q) gp tp t0 t1 t2 s0w (Z_to_bv 64 q) (Z_to_bv 64 sk) (Z_to_bv 64 ATH_CMP) a2 a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 (Z_to_bv 64 sk) s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 P_OPENSSL_sk_set_cmp_thunks) fc None m (seg_rom asegs))
        (MS (mkR rax (Z_to_bv 64 q) gp tp t0 t1 t2 s0w (Z_to_bv 64 q) (Z_to_bv 64 sk) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 ADE_R11)) fc None m (seg_rom asegs)).
  Proof.
    intros until sk. intros SKR Q0 QH MI. unfold ADE_R11, ADE_R12, ATH_CMP, P_OPENSSL_sk_set_cmp_thunks in *. retpc.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
    step. step. step. step. step. step. apply evt_done. reflexivity.
  Qed.
  (* [comment removed for export] *)
  Lemma ade_seg16 :
    forall (rax gp tp t0 t1 t2 s0w a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (q sk : Z),
      0 <= sk < 2^64 -> 0 <= q -> q + 312 < 2^64 -> mem_inv asegs m ->
      evt asegs (fun ms' =>
          ms' = MS (mkR (Z_to_bv 64 ADE_R13) (Z_to_bv 64 q) gp tp t0 t1 t2 s0w (Z_to_bv 64 q) (Z_to_bv 64 sk) (Z_to_bv 64 ATH_COPY) a2 a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 (Z_to_bv 64 sk) s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 P_OPENSSL_sk_set_copy_thunks) fc None m (seg_rom asegs))
        (MS (mkR rax (Z_to_bv 64 q) gp tp t0 t1 t2 s0w (Z_to_bv 64 q) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 (Z_to_bv 64 sk) s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 ADE_R12)) fc None m (seg_rom asegs)).
  Proof.
    intros until sk. intros SKR Q0 QH MI. unfold ADE_R12, ADE_R13, ATH_COPY, P_OPENSSL_sk_set_copy_thunks in *. retpc.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
    step. step. step. step. step. apply evt_done. reflexivity.
  Qed.
  (* [comment removed for export] *)
  Lemma ade_seg17 :
    forall (rax gp tp t0 t1 t2 s0w a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (q sk : Z),
      0 <= sk < 2^64 -> 0 <= q -> q + 312 < 2^64 -> mem_inv asegs m ->
      evt asegs (fun ms' =>
          ms' = MS (mkR (Z_to_bv 64 ADE_R14) (Z_to_bv 64 q) gp tp t0 t1 t2 s0w (Z_to_bv 64 q) (Z_to_bv 64 sk) (Z_to_bv 64 ATH_FREE) a2 a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 (Z_to_bv 64 sk) s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 P_OPENSSL_sk_set_thunks) fc None m (seg_rom asegs))
        (MS (mkR rax (Z_to_bv 64 q) gp tp t0 t1 t2 s0w (Z_to_bv 64 q) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 (Z_to_bv 64 sk) s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 ADE_R13)) fc None m (seg_rom asegs)).
  Proof.
    intros until sk. intros SKR Q0 QH MI. unfold ADE_R13, ADE_R14, ATH_FREE, P_OPENSSL_sk_set_thunks in *. retpc.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
    step. step. step. step. step. apply evt_done. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma ade_f53x :
    forall (rax gp tp t0 t1 t2 s0w a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (q line ee lbuf btmp Bb ff r16 : Z)
           (w24 w32 w40 w48 w56 w64 w72 w80 w88 w112 w128 w136 : word) (w152 w160 w168 w176 w184 w192 w224 w232 : word),
      rw_cells asegs m (q + 16) (arp_sg1 (wz r16) w24 w32 w40 w48 w56 w64 w72 w80 w88 (wz lbuf) (wz btmp) w112 (wz Bb) w128 w136) ->
      rw_cells asegs m (q + 144) (arp_sg2 (wz ee) w152 w160 w168 w176 w184 w192 (wz ff) (wz ff) (wz ASHB) w224 w232) ->
      0 <= r16 < 2^64 -> 0 <= ee < 2^64 -> 0 <= lbuf < 2^64 -> 0 <= btmp < 2^64 -> 0 <= Bb < 2^64 -> 0 <= ff < 2^64 ->
      0 <= q -> q + 312 < 2^64 -> mem_inv asegs m ->
      evt asegs (fun ms' =>
          ms' = MS (mkR rax (Z_to_bv 64 q) gp tp t0 t1 t2 s0w (Z_to_bv 64 q) a0 a1 a2 a3 a4 a5 a6 a7
                       (Z_to_bv 64 ee) s3 (Z_to_bv 64 r16) (Z_to_bv 64 line) (Z_to_bv 64 ff) (Z_to_bv 64 ff) (Z_to_bv 64 btmp) (Z_to_bv 64 Bb) (Z_to_bv 64 lbuf) s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 ADE_TX) fc None m (seg_rom asegs))
        (MS (mkR rax (Z_to_bv 64 q) gp tp t0 t1 t2 s0w (Z_to_bv 64 q) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 (Z_to_bv 64 line) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x51b4b4) fc None m (seg_rom asegs)).
  Proof.
    intros until w232. intros FA FB R16 EER LR BR BBR FFR Q0 QH MI. unfold ADE_TX in *. unfold arp_sg1, arp_sg2, ASHB, wz in FA, FB |- *.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
    do 7 step. step. apply evt_done. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma ade_seg18 :
    forall (rax gp tp t0 t1 t2 s0w a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (q sk ee es lbuf btmp Bb ff r16 z1 z2 h : Z)
           (w24 w32 w40 w48 w56 w64 w72 w80 w88 w112 w128 w136 : word) (w152 w160 w168 w176 w184 w224 w232 : word),
      rw_cells asegs m (q + 16) (arp_sg1 (wz r16) w24 w32 w40 w48 w56 w64 w72 w80 w88 (wz lbuf) (wz btmp) w112 (wz Bb) w128 w136) ->
      rw_cells asegs m (q + 144) (arp_sg2 (wz ee) w152 w160 w168 w176 w184 (wz es) (wz ff) (wz ff) (wz ASHB) w224 w232) ->
      rw_cells asegs m es [C8 (wz h); C8 (wz z1); C8 (wz z2)] -> 0 < es -> es + STORE_SIZE <= aceil -> accessible m es STORE_SIZE ->
      0 <= sk < 2^64 -> 0 <= r16 < 2^64 -> 0 <= ee < 2^64 -> 0 <= lbuf < 2^64 -> 0 <= btmp < 2^64 -> 0 <= Bb < 2^64 -> 0 <= ff < 2^64 ->
      aceil <= q -> q + 312 < 2^64 -> mem_inv asegs m ->
      evt asegs (fun ms' => exists m1,
          munch [(es, es + 8)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
          /\ rw_cells asegs m1 es [C8 (wz sk); C8 (wz z1); C8 (wz z2)] /\
         (  (sk = 0 /\
             ms' = MS (mkR rax (Z_to_bv 64 q) gp tp t0 t1 t2 s0w (Z_to_bv 64 q) (Z_to_bv 64 sk) (Z_to_bv 64 es) a2 a3 a4 a5 a6 a7
                           (Z_to_bv 64 ee) s3 (Z_to_bv 64 r16) (Z_to_bv 64 534) (Z_to_bv 64 ff) (Z_to_bv 64 ff) (Z_to_bv 64 btmp) (Z_to_bv 64 Bb) (Z_to_bv 64 lbuf) s11 t3 t4 t5 t6)
                      F (Z_to_bv 64 ADE_TX) fc None m1 (seg_rom asegs))
         \/ (0 < sk /\
             ms' = MS (mkR rax (Z_to_bv 64 q) gp tp t0 t1 t2 s0w (Z_to_bv 64 q) (Z_to_bv 64 sk) (Z_to_bv 64 es) a2 a3 a4 a5 a6 a7
                           s2 s3 (Z_to_bv 64 (Z.shiftr es 3 + ASHB)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                      F (Z_to_bv 64 ADE_PUSH) fc None m1 (seg_rom asegs))))
        (MS (mkR rax (Z_to_bv 64 q) gp tp t0 t1 t2 s0w (Z_to_bv 64 q) (Z_to_bv 64 sk) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 (Z_to_bv 64 (Z.shiftr es 3 + ASHB)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 ADE_R14)) fc None m (seg_rom asegs)).
  Proof.
    intros until w232. intros FA FB SC ESP ESH ACCS SKR R16 EER LR BR BBR FFR CQ QH MI.
    unfold ADE_R14, ADE_TX, ADE_PUSH in *. unfold arp_sg1, arp_sg2, ASHB, wz in FA, FB, SC |- *. unfold STORE_SIZE in ESH, ACCS. retpc.
    acb. pose proof ACCS as (_ & AHIS & _). unfold AAPP_HI in AHIS.
    pose proof (munch_refl [(es, es + 8)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    (* [comment removed for export] *)
    ck8_load ACCS es. step. if_false_by (ck1_bnez_false 0 eq_refl).
    step. clear ACCS. st1. step. if_cases K0; zify_cond K0.
    - assert (SK0 : sk = 0) by (revert K0; rewrite ?unsigned_lit by lia; lia). clear K0.
      (* [comment removed for export] *)
      step. do 7 step. step.
      apply evt_done. eexists. repeat match goal with |- _ /\ _ => split end; try eassumption. left. split; [exact SK0| reflexivity].
    - assert (SKP : 0 < sk) by (revert K0; rewrite ?unsigned_lit by lia; lia). clear K0.
      apply evt_done. eexists. repeat match goal with |- _ /\ _ => split end; try eassumption. right. split; [exact SKP| reflexivity].
  Qed.

  (* [comment removed for export] *)
  Lemma ade_segP :
    forall (rax gp tp t0 t1 t2 s0w a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (q stk ee : Z) (w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 : word),
      rw_cells asegs m (q + 144) (arp_sg2 (wz ee) w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232) ->
      0 <= stk < 2^64 -> 0 <= ee < 2^64 -> 0 <= q -> q + 312 < 2^64 -> mem_inv asegs m ->
      evt asegs (fun ms' =>
          ms' = MS (mkR (Z_to_bv 64 ADE_R15) (Z_to_bv 64 q) gp tp t0 t1 t2 s0w (Z_to_bv 64 q) (Z_to_bv 64 stk) (Z_to_bv 64 ee) a2 a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 P_OPENSSL_sk_push) fc None m (seg_rom asegs))
        (MS (mkR rax (Z_to_bv 64 q) gp tp t0 t1 t2 s0w (Z_to_bv 64 q) (Z_to_bv 64 stk) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 ADE_PUSH) fc None m (seg_rom asegs)).
  Proof.
    intros until w232. intros FB SR EER Q0 QH MI. unfold ADE_PUSH, ADE_R15, P_OPENSSL_sk_push in *. unfold arp_sg2, wz in FB.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
    step. step. step. apply evt_done. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma ade_seg20 :
    forall (rax gp tp t0 t1 t2 s0w a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (q prv cur ee lbuf btmp Bb ff r16 sh8 : Z)
           (w24 w32 w48 w56 w64 w72 w80 w88 w112 w128 w136 : word) (w152 w160 w168 w184 w192 w224 w232 : word),
      rw_cells asegs m (q + 16) (arp_sg1 (wz r16) w24 w32 (wz (cur + 4)) w48 w56 w64 w72 w80 w88 (wz lbuf) (wz btmp) w112 (wz Bb) w128 w136) ->
      rw_cells asegs m (q + 144) (arp_sg2 (wz ee) w152 w160 w168 (wz sh8) w184 w192 (wz ff) (wz ff) (wz ASHB) w224 w232) ->
      0 <= prv < 2^64 -> 0 <= r16 < 2^64 -> 0 <= ee < 2^64 -> 0 <= lbuf < 2^64 -> 0 <= btmp < 2^64 -> 0 <= Bb < 2^64 -> 0 <= ff < 2^64 ->
      0 <= cur -> cur + 4 < 2^64 -> 0 <= sh8 < 2^64 ->
      0 <= q -> q + 312 < 2^64 -> mem_inv asegs m ->
      evt asegs (fun ms' =>
            (prv = 0 /\
             ms' = MS (mkR rax (Z_to_bv 64 q) gp tp t0 t1 t2 s0w (Z_to_bv 64 q) (Z_to_bv 64 prv) a1 a2 a3 a4 a5 a6 a7
                           (Z_to_bv 64 ee) s3 (Z_to_bv 64 r16) (Z_to_bv 64 538) (Z_to_bv 64 ff) (Z_to_bv 64 ff) (Z_to_bv 64 btmp) (Z_to_bv 64 Bb) (Z_to_bv 64 lbuf) (Z_to_bv 64 sh8) t3 t4 t5 t6)
                      F (Z_to_bv 64 ADE_TX) fc None m (seg_rom asegs))
         \/ (prv <> 0 /\
             ms' = MS (mkR rax (Z_to_bv 64 q) gp tp t0 t1 t2 s0w (Z_to_bv 64 q) (Z_to_bv 64 prv) a1 a2 a3 a4 a5 a6 a7
                           (Z_to_bv 64 (cur + 4)) s3 s4 s5 s6 s7 s8 s9 s10 (Z_to_bv 64 sh8) t3 t4 t5 t6)
                      F (Z_to_bv 64 ADE_ADV) fc None m (seg_rom asegs)))
        (MS (mkR rax (Z_to_bv 64 q) gp tp t0 t1 t2 s0w (Z_to_bv 64 q) (Z_to_bv 64 prv) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 ADE_R15)) fc None m (seg_rom asegs)).
  Proof.
    intros until w232. intros FA FB PR R16 EER LR BR BBR FFR C0 CH SH8 Q0 QH MI.
    unfold ADE_R15, ADE_TX, ADE_ADV in *. unfold arp_sg1, arp_sg2, ASHB, wz in FA, FB |- *. retpc.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
    (* [comment removed for export] *)
    step. step. step. if_cases K0; zify_cond K0.
    - assert (P0 : prv = 0) by (revert K0; rewrite ?unsigned_lit by lia; lia). clear K0.
      (* [comment removed for export] *)
      step. step. do 7 step. step.
      apply evt_done. left. split; [exact P0| reflexivity].
    - assert (P1 : prv <> 0) by (revert K0; rewrite ?unsigned_lit by lia; lia). clear K0.
      apply evt_done. right. split; [exact P1| reflexivity].
  Qed.

  (* [comment removed for export] *)
  Lemma ade_skip1 :
    forall (rax spw gp tp t0 t1 t2 s0w s1w a0 a1 a2 a3 a4 a5 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (ee : Z),
      0 <= ee < 2^64 -> mem_inv asegs m ->
      evt asegs (fun ms' =>
          ms' = MS (mkR (Z_to_bv 64 ADE_SK_R1) spw gp tp t0 t1 t2 s0w s1w (Z_to_bv 64 ee) a1 a2 a3 a4 a5 (Z_to_bv 64 ee) a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_ossl_echstore_entry_free) fc None m (seg_rom asegs))
        (MS (mkR rax spw gp tp t0 t1 t2 s0w s1w a0 a1 a2 a3 a4 a5 (Z_to_bv 64 ee) a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 ADE_SKIP) fc None m (seg_rom asegs)).
  Proof.
    intros until ee. intros EER MI. unfold ADE_SKIP, ADE_SK_R1, P_ossl_echstore_entry_free in *.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
    step. step. apply evt_done. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma ade_skip2 :
    forall (rax gp tp t0 t1 t2 s0w a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (q SH : Z) (w144 w152 w160 w168 w184 w192 w200 w208 w224 w232 : word)
           (sa : list byte) (sb : byte) (sc sd se : list byte) (sr : byte) (sg : list byte),
      set_shadow_f8_stmt ->
      rw_cells asegs m (q + 144) (arp_sg2 w144 w152 w160 w168 (wz (SH + 8)) w184 w192 w200 w208 (wz ASHB) w224 w232) ->
      rw_cells asegs m SH (arp_fshadow sa sb sc sd se sr sg) ->
      ASHB + AIMG_TOP / 8 <= SH -> SH + 512 < AHI_LO ->
      aceil <= q -> q + 312 < 2^64 -> mem_inv asegs m -> ACONST m ->
      evt asegs (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m1,
          ms' = MS (mkR (Z_to_bv 64 ADE_SK_R2) (Z_to_bv 64 q) gp tp t0' t1' t2' s0w (Z_to_bv 64 q) (Z_to_bv 64 (-8)) a1' a2' a3' a4' a5' a6' a7'
                       s2 (Z_to_bv 64 SH) s4 s5 s6 (Z_to_bv 64 ASHB) s8 s9 s10 (Z_to_bv 64 (SH + 8)) t3' t4' t5' t6')
                   F (Z_to_bv 64 ADE_ADV) fc None m1 (seg_rom asegs)
          /\ munch [(SH + 4, SH + 5); (SH + 8, SH + 264)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
          /\ rw_cells asegs m1 SH (arp_fshadow sa (b8 0xf8) sc (poison_bytes 256 0xf8) se sr sg)
          /\ ACONST m1)
        (MS (mkR rax (Z_to_bv 64 q) gp tp t0 t1 t2 s0w (Z_to_bv 64 q) a0 a1 a2 a3 a4 a5 a6 a7
                 s2 (Z_to_bv 64 SH) s4 s5 s6 (Z_to_bv 64 ASHB) s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 ADE_SK_R1)) fc None m (seg_rom asegs)).
  Proof.
    intros until sg. intros SF8 FB FS SH1 SH2 CQ QH MI AC.
    unfold ADE_SK_R1, ADE_SK_R2, ADE_ADV in *. unfold arp_sg2, ASHB, wz in FB |- *. unfold arp_fshadow in FS |- *. retpc.
    unfold ASHB, AIMG_TOP in SH1. unfold AHI_LO in SH2. change (12386304 / 8) with 1548288 in SH1. pose proof aceil_range as ACR. acb.
    pose proof (munch_refl [(SH + 4, SH + 5); (SH + 8, SH + 264)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    (* [comment removed for export] *)
    step. step. step. step. step.
    lazymatch goal with FSx : rw_cells asegs ?mx SH (?c1 :: ?c2 :: ?c3 :: ?c4 :: ?rest) |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      pose proof FSx as SHC; change (rw_cells asegs mx SH ([c1; c2; c3] ++ (c4 :: rest))) in SHC; clear FSx end.
    apply (proj1 (rw_cells_app _ _ _ _ _)) in SHC. destruct SHC as [SH3 SHR4]. cbn [cells_size csize Nat.add] in SHR4. change (Z.of_nat 8) with 8 in SHR4.
    lazymatch type of SHR4 with rw_cells _ ?mx _ (?c4 :: ?rest) => change (rw_cells asegs mx (SH + 8) ([c4] ++ rest)) in SHR4 end.
    apply (proj1 (rw_cells_app _ _ _ _ _)) in SHR4. destruct SHR4 as [SH256 SHT]. cbn [cells_size csize Nat.add] in SHT. change (Z.of_nat 256) with 256 in SHT.
    eapply evt_cut.
    { unfold set_shadow_f8_stmt, set_shadow_stmt in SF8. eapply SF8 with (n := 256); [reflexivity| reflexivity| lia| change (Z.to_nat 256) with 256%nat; exact SH256| assumption| exact AC]. }
    cbv beta. intros ms1 PO. unfold set_shadow_post in PO.
    destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & mA & -> & MU1 & WM1 & MI1 & SH256').
    retpc. clear SH256. aland MU1 WM1.
    (* [comment removed for export] *)
    step. st1. step.
    finish.
    { lazymatch goal with |- rw_cells _ ?mx ?base _ =>
        lazymatch goal with A : rw_cells _ mx base [_; _; _], B : rw_cells _ mx (base + 8) [_], C : rw_cells _ mx (base + 8 + 256) _ |- _ =>
            change (Z.to_nat 256) with 256%nat in B;
            pose proof (proj2 (rw_cells_app asegs mx (base + 8) [CB 256 (poison_bytes 256 248)] _) (conj B ltac:(cbn [cells_size csize Nat.add]; change (Z.of_nat 256) with 256; exact C))) as BC;
            cbn [app] in BC;
            pose proof (proj2 (rw_cells_app asegs mx base _ _) (conj A ltac:(cbn [cells_size csize Nat.add]; change (Z.of_nat 8) with 8; exact BC))) as ABC;
            cbn [app] in ABC; exact ABC end end. }
    eapply ACONST_frame; [exact AC| exact MU| exact WM|].
    apply Forall_cons; [apply aconst_ok_high; cbn [fst snd]; unfold sh, AIMG_TOP; rewrite ?ASHADOW_BASE_val; lia|].
    apply Forall_cons; [apply aconst_ok_high; cbn [fst snd]; unfold sh, AIMG_TOP; rewrite ?ASHADOW_BASE_val; lia| apply Forall_nil].
  Qed.
End S.
