(* reloc-zl14c a0d38446bd9d1007b9d78c8c99a773db *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Lib Require Import Arr Bytes ZBridge Tac InitMem StoreFast.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Spec Require Import AsanCtrl.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.AsanW Require Import AImg RtCells ABase ABytes AMalloc_iface AUri_kit.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.zspec.zmodel Require Import ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.IK Require Import IDefs.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.U2A Require Import U2AShadow U2AKit U2AArr U2AStore InfAGlue InfPure.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.U3A Require Import U2AObj U2AClient U2AIface InfABase InfAKit.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.LibA Require Import StepF.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac solve_load ::= first [ solve_load_sh0 | solve_load_shlit | solve_load_base | solve_load_image ].
Local Ltac acc_hint ::= acc_hint_sh.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= farr_store_extra m a bs n Hn Ha Hl.
Local Ltac transport_call_extra segs W m m' MU WM ::= farr_call_extra segs W m m' MU WM.

(* [comment removed for export] *)
Lemma reach_cases : forall m, reach m ->
  m = HEAD \/ m = DICTID \/ m = DICT \/ m = TYPE \/ m = TYPEDO \/ m = STORED \/ m = COPY_ \/ m = COPY \/
  m = TABLE \/ m = LENLENS \/ m = CODELENS \/ m = LEN_ \/ m = LEN \/ m = LENEXT \/ m = DIST \/ m = DISTEXT \/
  m = MATCH \/ m = LIT \/ m = CHECK \/ m = LENGTH \/ m = DONE \/ m = BAD \/ m = MEM.
Proof. intros m H. unfold reach in H. cbv [HEAD DICTID DICT TYPE TYPEDO STORED COPY_ COPY TABLE LENLENS CODELENS LEN_ LEN LENEXT DIST DISTEXT MATCH LIT CHECK LENGTH DONE BAD MEM] in *. lia. Qed.

Section CANSEC1. Context {rc : runConstT}.
Section S.
  Variable AI : AMallocIface.
  Variables (L : alayout) (RNG : footprint) (stA : astate) (LB : list ablock).
  Variables (gp tp : word) (FR : bvmap 5 word) (fc : bv 32) (POST : machine_state -> Prop).
  Variables (LBc : list ablock) (m0 : amem) (payload : list Z) (fw : Z -> Z) (saved fk fksh : list cell).

  Notation KDISPB cx ly B := (KDISP cx ly AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh B).
  Notation KBADB cx ly B := (KBADMODE cx ly AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh B).
  Notation KLLD cx ly := (KLEAVE_LD cx ly AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh).
  Notation KLV cx ly := (KLEAVE cx ly AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh).
  Notation KALLB cx ly B := (KALL cx ly AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh B).
  Notation ARM cx ly Lb X := (arm_stmtA cx ly AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh Lb X).

  (* [comment removed for export] *)
  Lemma kbadmode_of_kdisp : forall cx ly B, inf_ctx cx ly AI RNG LB -> Z.of_nat (length payload) = c_n cx -> KDISPB cx ly B -> KBADB cx ly B.
  Proof.
    intros cx ly B CTX PLEN KD. unfold KBADMODE. intros until m. intros SI ME ARR VIS HID.
    pose proof (proj1 SI : IDefs.RNG cx st lf cf) as RN0.
    inf_arm_open_rn.
    zrunb [0x8e2ec].
    eapply (KD (bad_of (IST mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)) lf cf wf fo);
      [exact SI| exact ME| exact ARR| unfold bad_of; change BAD with 16209; inf_vis_close| inf_hid_close].
    (* [U14] v240 is a vestige binder of KDISP at 1.4 (InfABase's inf_locals no longer holds it) *)
    Unshelve. all: exact (Z_to_bv 64 0).
  Qed.

  (* [comment removed for export] *)
  Lemma kleave_ld_of_kleave : forall cx ly, inf_ctx cx ly AI RNG LB -> Z.of_nat (length payload) = c_n cx -> KLV cx ly -> KLLD cx ly.
  Proof.
    (* pc-inflate 2026-11-17, UNPATCHED: the arm site loads the return code itself, so KLEAVE_LD is the join with
       s8 = t_ret st (InfABase), an instance of KLEAVE *)
    intros cx ly CTX PLEN KL. unfold KLEAVE_LD. intros until m. intros SI ARR VIS HID.
    assert (EL : L_LEAVE_LD = L_LEAVE) by reflexivity. rewrite EL.
    exact (KL st (t_ret st) lf cf wf fo v0 v8 v16 v240 v504 vnext j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3
              havedict dmax check total shold sbits back was pad x1 x5 x6 x7 x11 x12 x13 x14 x15 x17 x22 x28 x31 m SI ARR VIS HID).
  Qed.

  (* [comment removed for export] *)
  Section Step.
  Hypothesis PAYR : Forall (fun c => 0 <= c < 256) payload.
  (* [comment removed for export] *)
  Definition arms_ok (cx : ictx) (ly : ilay) : Prop :=
       ARM cx ly 0x8e340 HEAD
    /\ ARM cx ly 0x8e88c DICTID
    /\ ARM cx ly 0x8ed70 DICT
    /\ ARM cx ly 0x8ee10 TYPE
    /\ ARM cx ly 0x8ee20 TYPEDO
    /\ ARM cx ly 0x8e95c STORED
    /\ ARM cx ly 0x8efdc COPY_
    /\ ARM cx ly 0x8eff4 COPY
    /\ ARM cx ly 0x8e3d4 TABLE
    /\ ARM cx ly 0x8eb30 LENLENS
    /\ ARM cx ly 0x8f464 CODELENS
    /\ ARM cx ly 0x90cb0 LEN_
    /\ ARM cx ly 0x90cc8 LEN
    /\ ARM cx ly 0x8e464 LENEXT
    /\ ARM cx ly 0x9122c DIST
    /\ ARM cx ly 0x8e440 DISTEXT
    /\ ARM cx ly 0x91680 MATCH
    /\ ARM cx ly 0x8e828 LIT
    /\ ARM cx ly 0x8e9d4 CHECK
    /\ ARM cx ly 0x90248 LENGTH.

  Lemma kall_of_kdisp : forall cx ly B, inf_ctx cx ly AI RNG LB -> Z.of_nat (length payload) = c_n cx -> KLV cx ly -> KDISPB cx ly B -> KALLB cx ly B.
  Proof.
    intros cx ly B CTX PLEN KL KD. unfold KALL. split; [exact KD|]. split; [apply kbadmode_of_kdisp; assumption|].
    split; [apply kleave_ld_of_kleave; assumption| exact KL].
  Qed.

  Lemma kdisp_mono : forall cx ly B B', B' <= B -> KDISPB cx ly B -> KDISPB cx ly B'.
  Proof. intros cx ly B B' HB KD. unfold KDISP. intros until m. intros SI ME. apply KD; [exact SI| lia]. Qed.

  Lemma kdisp_step : forall cx ly B, inf_ctx cx ly AI RNG LB -> Z.of_nat (length payload) = c_n cx -> KLV cx ly -> arms_ok cx ly -> KDISPB cx ly B -> KDISPB cx ly (B + 1).
  Proof.
    intros cx ly B CTX PLEN KL ARMS KD. unfold KDISP, DISP_MS, L_DISP. intros until m. intros SI ME ARR VIS HID.
    assert (KA : KALLB cx ly (meas cx st)).
    { apply kall_of_kdisp; [exact CTX| exact PLEN| exact KL|]. eapply kdisp_mono; [| exact KD]. lia. }
    clear KD.
    pose proof SI as (_ & _ & _ & MO). pose proof (reach_cases _ (proj1 MO)) as CASES. clear MO.
    inf_arm_open.
    destruct ARMS as (A_HEAD & A_DICTID & A_DICT & A_TYPE & A_TYPEDO & A_STORED & A_COPY_ & A_COPY & A_TABLE & A_LENLENS & A_CODELENS & A_LEN_ & A_LEN & A_LENEXT & A_DIST & A_DISTEXT & A_MATCH & A_LIT & A_CHECK & A_LENGTH).
    cbv [HEAD DICTID DICT TYPE TYPEDO STORED COPY_ COPY TABLE LENLENS CODELENS LEN_ LEN LENEXT DIST DISTEXT MATCH LIT CHECK LENGTH DONE BAD MEM] in CASES, MNE.
    (* [comment removed for export] *)
    assert (MR : 16180 <= mode <= 16210) by (clear - CASES; lia).
    zrunb [0x8e30c].
    setreg 11 (Z_to_bv 64 (mode - 16180))
      ltac:(rewrite <- (Z_to_bv_mod64 (mode + 18446744073709535436)), <- (Z_to_bv_mod64 (mode - 16180)); f_equal;
            replace (mode + 18446744073709535436) with (mode - 16180 + 1 * 2 ^ 64) by lia; symmetry; apply Z_mod_plus_full).
    zrunb [0x8e324].
    Local Ltac fold_reg_lit r :=
      let w := getreg r in
      lazymatch w with Z_to_bv 64 ?e => let v := eval vm_compute in e in is_Zlit v; change e with v end.
    Local Ltac disp Lb := fold_reg_lit 11; zrunb [Lb].
    Local Ltac arm A :=
      lazymatch goal with
      | SI : sinv ?cx0 ?st0 ?lf0 ?cf0, KA : KALL ?cx0 ?ly0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
          eapply (A st0 lf0 cf0);
            [ lazymatch goal with H : inf_ctx _ _ _ _ _ |- _ => exact H end | assumption | assumption | reflexivity | exact SI | eassumption
            | inf_vis_close | inf_hid_close | exact KA ]
      end.
    decompose [or] CASES; clear CASES; match goal with Hc : mode = _ |- _ => rewrite Hc in *; clear Hc; try clear mode end.
    - disp 0x8e340. arm A_HEAD.
    - disp 0x8e88c. arm A_DICTID.
    - disp 0x8ed70. arm A_DICT.
    - disp 0x8ee10. arm A_TYPE.
    - disp 0x8ee20. arm A_TYPEDO.
    - disp 0x8e95c. arm A_STORED.
    - disp 0x8efdc. arm A_COPY_.
    - disp 0x8eff4. arm A_COPY.
    - disp 0x8e3d4. arm A_TABLE.
    - disp 0x8eb30. arm A_LENLENS.
    - disp 0x8f464. arm A_CODELENS.
    - disp 0x90cb0. arm A_LEN_.
    - disp 0x90cc8. arm A_LEN.
    - disp 0x8e464. arm A_LENEXT.
    - disp 0x9122c. arm A_DIST.
    - disp 0x8e440. arm A_DISTEXT.
    - disp 0x91680. arm A_MATCH.
    - disp 0x8e828. arm A_LIT.
    - disp 0x8e9d4. arm A_CHECK.
    - disp 0x90248. arm A_LENGTH.
    - (* [comment removed for export] *)
      zrunb [0x928f8].   (* pc-inflate 2026-11-17, UNPATCHED: the leave join *)
      destruct KA as (_ & _ & _ & KLV0).
      eapply (KLV0 (IST 16208 last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) 1 lf cf wf fo);
        [exact SI| exact ARR| inf_vis_close| inf_hid_close].
    - (* [comment removed for export] *)
      zrunb [0x928f8].   (* pc-inflate 2026-11-17, UNPATCHED: the leave join *)
      destruct KA as (_ & _ & _ & KLV0).
      eapply (KLV0 (IST 16209 last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) (-3) lf cf wf fo);
        [exact SI| exact ARR| inf_vis_close| inf_hid_close].
    - (* [comment removed for export] *) exfalso. lia.
    (* [U14] v240 is a vestige binder at 1.4 (InfABase's inf_locals no longer holds it) *)
    Unshelve. all: exact (Z_to_bv 64 0).
  Qed.

  (* [comment removed for export] *)
  Lemma loop_nat : forall cx ly (k : nat), inf_ctx cx ly AI RNG LB -> Z.of_nat (length payload) = c_n cx -> KLV cx ly -> arms_ok cx ly -> KDISPB cx ly (Z.of_nat k).
  Proof.
    intros cx ly k CTX PLEN KL ARMS. induction k as [|k IH].
    - unfold KDISP. intros until m. intros SI ME. exfalso. pose proof (meas_nonneg _ _ _ _ SI). cbn [Z.of_nat] in ME. lia.
    - rewrite Nat2Z.inj_succ. apply kdisp_step; assumption.
  Qed.

  Theorem loop_kdisp : forall cx ly B, inf_ctx cx ly AI RNG LB -> Z.of_nat (length payload) = c_n cx -> KLV cx ly -> arms_ok cx ly -> KDISPB cx ly B.
  Proof. intros cx ly B CTX PLEN KL ARMS. apply (kdisp_mono cx ly (Z.of_nat (Z.to_nat B))); [lia| apply loop_nat; assumption]. Qed.

  Theorem loop_kall : forall cx ly B, inf_ctx cx ly AI RNG LB -> Z.of_nat (length payload) = c_n cx -> KLV cx ly -> arms_ok cx ly -> KALLB cx ly B.
  Proof. intros cx ly B CTX PLEN KL ARMS. apply kall_of_kdisp; [exact CTX| exact PLEN| exact KL| apply loop_kdisp; assumption]. Qed.
  End Step.
End S.
End CANSEC1.
