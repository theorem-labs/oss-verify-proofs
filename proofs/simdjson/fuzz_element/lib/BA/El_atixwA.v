From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS StoreFast FP SysStep.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim StrFun.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjTape SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Str_tac Sj_h_arith Sj_stage1_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout RT_iface. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import RT_iface2. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import D_defs D_kit D_clx D_rlkit Sj_rtf Sj_akit Sj_acps Sj_hkit. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import Atp_defsA Atp_kitA El_callsA El_atixdA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition atix_set_site (ra' : Z) : Prop := ra' = 0xb397c \/ ra' = 0xb39d0.

Lemma sub_fp_atixW : forall q out, sub_fp [(out, out + 24)] (atix_W q out).
Proof. intros q out x Hx. unfold atix_W in Hx. cbn [outside] in *. lia. Qed.

Ltac notpcX z := lazymatch goal with
  | |- evt _ _ (MS _ _ (Z_to_bv _ ?p) _ _ _ _) => assert_fails (assert (p = z) by (vm_compute; reflexivity))
  | _ => idtac end.
Ltac runtoX z := repeat (notpcX z; notmsX; first [ stX | ifkX ]).
Ltac runoX z SHZO out := repeat (notpcX z; notmsX;
  first [ stX | ifkX | (shz_pose SHZO out; shz_pose SHZO (out + 8); shz_pose SHZO (out + 16); stX) ]).

Ltac atix_set_done MU WM FR1 :=
  apply evt_done; left; do 15 eexists;
  split; [exact MU|]; split; [exact WM|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|];
  split; [exact FR1|]; split; [unfold entry_st, e_asan_memset; atp_st_eq_goal| unfold atix_set_site; lia].

Section AtIxW.
  Variable E : aenvA.
  Hypothesis OK : aenvA_ok E.

  Definition atix_x1 (q out : Z) (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (jo : list byte) : machine_state -> Prop :=
    fun ms =>
      (exists (m1 : mem) (j0 : list byte) (ra' : Z) (t0' t1' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
         munch (atix_W q out) m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ rw_cells asegs m1 out [CB 24 jo] /\
         stk asegs m1 (ae_lo E) (q + -32) /\ rw_cells asegs m1 (q + -32) (atix_frame ra s0 s1 j0) /\
         ms = entry_st (wz ra') (wz (q + -32)) gp (wz TPV) t0' t1' t2' (wz (out + 16)) (wz 2147450880) (wz out) (wz 0) (wz 16)
                       a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6' F fc e_asan_memset m1 /\
         atix_set_site ra')
   \/
      (exists (m1 : mem) (jo' : list byte) (y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
         munch (atix_W q out) m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ rw_cells asegs m1 out [CB 24 jo'] /\
         stk asegs m1 (ae_lo E) q /\
         ms = MS (mkR ra (wz q) gp (wz TPV) y5 y6 y7 s0 s1 y10 y11 y12 y13 y14 y15 y16 y17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31)
                 F (ret_pc ra) fc None m1 (seg_rom asegs)).

  Lemma atix_epi : forall (K : machine_state -> Prop) (m : mem) (F : bvmap 5 word) (fc : bv 32) (q : Z)
      (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (j0 : list byte)
      (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
    rw_cells asegs m (q + -32) (atix_frame ra s0 s1 j0) -> stk asegs m (ae_lo E) (q + -32) -> mem_inv asegs m -> ae_lo E <= q + -32 ->
    (forall (y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word), stk asegs m (ae_lo E) q ->
       K (MS (mkR ra (wz q) gp (wz TPV) y5 y6 y7 s0 s1 y10 y11 y12 y13 y14 y15 y16 y17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31)
             F (ret_pc ra) fc None m (seg_rom asegs))) ->
    evt asegs K (MS (mkR x1 (wz (q + -32)) gp (wz TPV) x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
                         s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                    F (wz 0xb39e8) fc None m (seg_rom asegs)).
  Proof.
    intros until x31. intros FR ST MI LO HK. unfold atix_frame in FR.
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
    do 3 step. step.
    release_frame FR ST q.
    step. apply evt_done. apply HK. exact ST.
  Qed.

  Lemma atix_found : forall (K : machine_state -> Prop) (m : mem) (F : bvmap 5 word) (fc : bv 32) (it q out : Z)
      (ra s0 s1 x1 x3 x5 x6 x7 x8 x12 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31 : word) (j0 jo : list byte),
    rw_cells asegs m (q + -32) (atix_frame ra s0 s1 j0) -> stk asegs m (ae_lo E) (q + -32) -> mem_inv asegs m ->
    rw_cells asegs m out [CB 24 jo] ->
    ae_lo E + 64 <= q -> q <= out -> out + 24 <= ae_hi E -> out mod 8 = 0 -> q mod 16 = 0 -> 0 <= it < 2^32 ->
    (forall m', munch [(out, out + 24)] m m' -> wmono asegs m m' -> shz m' out 24) ->
    (forall (m' : mem) (jo' : list byte) (y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
       munch [(out, out + 24)] m m' -> wmono asegs m m' -> mem_inv asegs m' -> stk asegs m' (ae_lo E) q ->
       rw_cells asegs m' out [CB 24 jo'] ->
       K (MS (mkR ra (wz q) x3 (wz TPV) y5 y6 y7 s0 s1 y10 y11 y12 y13 y14 y15 y16 y17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31)
             F (ret_pc ra) fc None m' (seg_rom asegs))) ->
    evt asegs K (MS (mkR x1 (wz (q + -32)) x3 (wz TPV) x5 x6 x7 x8 (wz 2147450880)
                         (wz out) (wz (ae_DOC E)) x12 (wz it) x14 x15 x16 x17
                         s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31) F (wz 0xb3a8c) fc None m (seg_rom asegs)).
  Proof using OK.
    intros until jo. intros FR ST MI OUT LO QO OB O8 Q16 ITR SHZO HK.
    pose proof OK as OK'. destruct OK' as [WF SBS P1 P1L [T16 [NT8 [TN [TS TL]]]] _ PTRR P0' [D8 [DF [DL [DS DT]]]] LOW [HL HT]].
    unfold SEGTOP_A, USTACK_TOP in *. unfold atix_frame in FR.
    apply (rw_cells_split_CB asegs _ _ [] 24 jo [] [8; 8; 4; 4]%nat) in OUT; [| reflexivity]. cbn [mk_CB_cells app] in OUT.
    lazymatch type of OUT with rw_cells _ _ _ [CB 8 ?xa; CB 8 ?xb; CB 4 ?xc; CB 4 ?xd] =>
      set (oa := xa) in OUT; set (ob := xb) in OUT; set (oc := xc) in OUT; set (od := xd) in OUT end.
    clearbody oa ob oc od.
    pose proof (munch_refl [(out, out + 24)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    runoX 0xb39e8 SHZO out.
    name_mem m2.
    lazymatch goal with H : rw_cells asegs m2 (q + -32) _ |- _ => rename H into FR2 end.
    lazymatch goal with H : stk asegs m2 _ _ |- _ => rename H into ST2 end.
    lazymatch goal with H : mem_inv asegs m2 |- _ => rename H into MI2 end.
    lazymatch goal with H : rw_cells asegs m2 out _ |- _ => rename H into OUT2 end.
    eapply atix_epi; [unfold atix_frame; exact FR2| exact ST2| exact MI2| lia|].
    intros until y31. intros ST3. destruct (rw_cells_forget asegs m2 out _ OUT2) as (jo' & OUT3).
    exact (HK m2 jo' y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 MU WM MI2 ST3 OUT3).
  Qed.

  Lemma atix_after_set : forall (K : machine_state -> Prop) (m : mem) (F : bvmap 5 word) (fc : bv 32) (q out ra' : Z)
      (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (j0 zb j1 j2 : list byte)
      (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
    rw_cells asegs m (q + -32) (atix_frame ra s0 s1 j0) -> stk asegs m (ae_lo E) (q + -32) -> mem_inv asegs m ->
    rw_cells asegs m out [CB 16 zb; CB 4 j1; CB 4 j2] ->
    ae_lo E + 64 <= q -> q <= out -> out + 24 <= ae_hi E -> out mod 8 = 0 -> q mod 16 = 0 -> atix_set_site ra' ->
    (forall m', munch [(out, out + 24)] m m' -> wmono asegs m m' -> shz m' out 24) ->
    (forall (m' : mem) (jo' : list byte) (y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
       munch [(out, out + 24)] m m' -> wmono asegs m m' -> mem_inv asegs m' -> stk asegs m' (ae_lo E) q ->
       rw_cells asegs m' out [CB 24 jo'] ->
       K (MS (mkR ra (wz q) gp (wz TPV) y5 y6 y7 s0 s1 y10 y11 y12 y13 y14 y15 y16 y17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31)
             F (ret_pc ra) fc None m' (seg_rom asegs))) ->
    evt asegs K (MS (mkR (wz ra') (wz (q + -32)) gp (wz TPV) x5 x6 x7 (wz (out + 16)) (wz 2147450880)
                         x10 x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                    F (wz ra') fc None m (seg_rom asegs)).
  Proof using OK.
    intros until x31. intros FR ST MI OUT LO QO OB O8 Q16 SITE SHZO HK.
    pose proof OK as OK'. destruct OK' as [WF SBS P1 P1L [T16 [NT8 [TN [TS TL]]]] _ PTRR P0' [D8 [DF [DL [DS DT]]]] LOW [HL HT]].
    unfold SEGTOP_A, USTACK_TOP in *. unfold atix_frame in FR.
    pose proof (munch_refl [(out, out + 24)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    unfold atix_set_site in SITE.
    destruct SITE as [-> | ->].
    - runoX 0xb39e8 SHZO out.
      name_mem m2.
      lazymatch goal with H : rw_cells asegs m2 (q + -32) _ |- _ => rename H into FR2 end.
      lazymatch goal with H : stk asegs m2 _ _ |- _ => rename H into ST2 end.
      lazymatch goal with H : mem_inv asegs m2 |- _ => rename H into MI2 end.
      lazymatch goal with H : rw_cells asegs m2 out _ |- _ => rename H into OUT2 end.
      eapply atix_epi; [unfold atix_frame; exact FR2| exact ST2| exact MI2| lia|].
      intros until y31. intros ST3. destruct (rw_cells_forget asegs m2 out _ OUT2) as (jo' & OUT3).
      exact (HK m2 jo' y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 MU WM MI2 ST3 OUT3).
    - runoX 0xb39e8 SHZO out.
      name_mem m2.
      lazymatch goal with H : rw_cells asegs m2 (q + -32) _ |- _ => rename H into FR2 end.
      lazymatch goal with H : stk asegs m2 _ _ |- _ => rename H into ST2 end.
      lazymatch goal with H : mem_inv asegs m2 |- _ => rename H into MI2 end.
      lazymatch goal with H : rw_cells asegs m2 out _ |- _ => rename H into OUT2 end.
      eapply atix_epi; [unfold atix_frame; exact FR2| exact ST2| exact MI2| lia|].
      intros until y31. intros ST3. destruct (rw_cells_forget asegs m2 out _ OUT2) as (jo' & OUT3).
      exact (HK m2 jo' y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 MU WM MI2 ST3 OUT3).
  Qed.

  Ltac atix_tail IH XN :=
    runX; let KE := fresh "KE" in if_cases KE; zify_cond KE; cbv_concl_iota;
    [ eapply evt_eq; [| eapply IH]; [atp_st_eq | eassumption | lia | lia | lia]
    | step; eapply evt_eq; [| eapply XN]; atp_st_eq ].

  Lemma atix_loop : forall (K : machine_state -> Prop) (m : mem) (F : bvmap 5 word) (fc : bv 32) (d' : nat) (e q out : Z)
      (x1 x3 x8 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 : word),
    AINV_A E m -> shz m (ae_TAPE E) (8 * ae_n E) -> e + 1 <= ae_n E - 1 ->
    (forall (it : Z) (y12 y16 y28 y29 y30 y31 : word), 0 <= it < e ->
       evt asegs K (MS (mkR x1 (wz (q + -32)) x3 (wz TPV) (wz 4294967295) (wz 67240448) (wz 4294967297) x8 (wz 2147450880)
                            (wz out) (wz (ae_DOC E)) y12 (wz it) (wz (ae_TAPE E)) (wz e) y16 (wz 32)
                            x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 y28 y29 y30 y31) F (wz 0xb3a8c) fc None m (seg_rom asegs))) ->
    (forall (y12 y13 y16 y28 y29 y30 y31 : word),
       evt asegs K (MS (mkR x1 (wz (q + -32)) x3 (wz TPV) (wz 4294967295) (wz 67240448) (wz 4294967297) x8 (wz 2147450880)
                            (wz out) (wz (ae_DOC E)) y12 y13 (wz (ae_TAPE E)) (wz e) y16 (wz 32)
                            x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 y28 y29 y30 y31) F (wz 0xb39c0) fc None m (seg_rom asegs))) ->
    forall (n : nat) (it c' : Z) (y12 y16 y28 y29 y30 y31 : word),
      tiles (elem (ae_T E) (ae_S E) (ae_sn E) ck_any d') it e c' -> it <> e -> 0 <= it -> e - it <= Z.of_nat n ->
      evt asegs K (MS (mkR x1 (wz (q + -32)) x3 (wz TPV) (wz 4294967295) (wz 67240448) (wz 4294967297) x8 (wz 2147450880)
                           (wz out) (wz (ae_DOC E)) y12 (wz it) (wz (ae_TAPE E)) (wz e) y16 (wz 32)
                           x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 y28 y29 y30 y31) F (wz 0xb3a20) fc None m (seg_rom asegs)).
  Proof using OK.
    intros K m F fc d' e q out x1 x3 x8 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 AI SHZT EN XF XN.
    pose proof OK as OK'. destruct OK' as [WF SBS P1 P1L [T16 [NT8 [TN [TS TL]]]] _ PTRR P0' [D8 [DF [DL [DS DT]]]] LOW [HL HT]].
    unfold SEGTOP_A, USTACK_TOP in *.
    pose proof (tape_wf_root _ _ _ _ _ WF) as [_ NR].
    assert (HSN : ae_sn E < 2^56) by (destruct WF as (_ & ? & _); lia).
    pose proof AI as (TAPEB & _ & _ & DOCC & _).
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
    induction n as [|n IH]; intros it c' y12 y16 y28 y29 y30 y31 TI NE I0 FUEL.
    { pose proof (tiles_le _ (elem_lt _ _ _ _ d') _ _ _ TI). lia. }
    pose proof (tiles_le _ (elem_lt _ _ _ _ d') _ _ _ TI) as [ITE CC].
    destruct (array_iter (ae_T E) (ae_S E) (ae_sn E) ck_any (fun c cv H => H) HSN d' it e c' TI NE I0 ltac:(lia)) as (j' & EL & IJ & AFT & TI').
    clear AFT.
    pose proof (tape_read _ (ae_TAPE E) (ae_tws E) it TAPEB ltac:(lia)) as RDT.
    pose proof (elem_word_range _ _ _ _ _ _ EL I0 ltac:(lia) HSN) as TIR.
    shz_pose SHZT (ae_TAPE E + 8 * it).
    assert (TTR : 0 <= ttype (ae_T E it) < 256) by (unfold ttype; lia).
    runX.
    if_cases KC; cbv_concl_iota.
    { eapply evt_eq; [| eapply XF]; [atp_st_eq| lia]. }
    clear KC.
    destruct (elem_view_of (ae_T E) (ae_S E) (ae_sn E) ck_any (fun c cv H => H) HSN d' it j' EL I0 ltac:(lia))
      as [TY Ej|TY Ej|TY Ej STR|d2 e2 c2 Ed TY Ej NXT CLOSE TILES|d2 e2 c2 Ed TY Ej NXT CLOSE TILES];
      unfold ty in TY; subst j'; cbv [t_true t_false t_null t_i64 t_u64 t_dbl t_str t_arr t_obj] in TY.
    - destruct TY as [TY|[TY|TY]]; atix_tail IH XN.
    - destruct TY as [TY|[TY|TY]]; atix_tail IH XN.
    - atix_tail IH XN.
    - atix_tail IH XN.
    - atix_tail IH XN.
  Qed.

  Lemma atix_walk1 : forall (d : nat) (i j idx q out node : Z)
      (ra gp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (jo : list byte),
    elem (ae_T E) (ae_S E) (ae_sn E) ck_any d i j -> 0 <= i -> j <= ae_n E - 1 -> 0 <= idx < 2^64 ->
    AINV_A E m ->
    rw_cells asegs m node [C8 (wz (ae_DOC E)); C8 (wz i)] -> 0 < node -> node + 16 <= ae_lo E -> node mod 8 = 0 ->
    rw_cells asegs m out [CB 24 jo] -> q <= out -> out + 24 <= ae_hi E -> out mod 8 = 0 ->
    mem_inv asegs m -> stk asegs m (ae_lo E) q -> ae_lo E + 64 <= q -> q mod 16 = 0 -> shb_cells m ->
    (forall m', munch (atix_W q out) m m' -> wmono asegs m m' -> shz m' node 16) ->
    (forall m', munch (atix_W q out) m m' -> wmono asegs m m' -> shz m' (ae_DOC E) 16) ->
    (forall m', munch (atix_W q out) m m' -> wmono asegs m m' -> shz m' (ae_TAPE E) (8 * ae_n E)) ->
    (forall m', munch (atix_W q out) m m' -> wmono asegs m m' -> shz m' out 24) ->
    evt asegs (atix_x1 q out ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m jo)
      (atix_entry ra q gp t0 t1 t2 s0 s1 out node idx a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m).
  Proof using OK.
    intros until jo. intros EL I0 JN IDX AI NODE N0 NLO N8 OUT QO OB O8 MI ST LO Q16 [G1 G2] SHZN SHZD SHZT SHZO.
    pose proof OK as OK'. destruct OK' as [WF SBS P1 P1L [T16 [NT8 [TN [TS TL]]]] _ PTRR P0' [D8 [DF [DL [DS DT]]]] LOW [HL HT]].
    unfold atix_entry, ATIX_FN_A, SEGTOP_A, USTACK_TOP in *.
    assert (FS : 0 <= fs_size (ae_kD E)) by (unfold fs_size; apply Z.shiftl_nonneg; lia).
    pose proof (tape_wf_root _ _ _ _ _ WF) as [_ NR].
    assert (HSN : ae_sn E < 2^56) by (destruct WF as (_ & ? & _); lia).
    pose proof (elem_lt _ _ _ _ _ _ _ EL) as IJ.
    pose proof (munch_refl (atix_W q out) m) as MU. pose proof (wmono_refl asegs m) as WM. unfold atix_W in MU.
    pose proof (elem_word_range _ _ _ _ _ _ EL I0 ltac:(lia) HSN) as TIR.
    assert (TTR : 0 <= ttype (ae_T E i) < 256) by (unfold ttype; lia).
    step. carve_frame 32%nat ST.
    apply (rw_cells_split_CB asegs _ _ [] 32 junk [] [8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
    repeat match type of FR with context [CB 8 (firstn ?a ?b)] => let j := fresh "jk" in set (j := firstn a b) in FR; clearbody j end.
    do 6 step.
    name_mem m1.
    assert (AI1 : AINV_A E m1) by (apply (AINV_A_munch E _ m m1 OK AI MU); constructor; [cbn; lia|]; constructor; [cbn; lia| constructor]).
    pose proof AI1 as (TAPEB1 & _ & _ & DOCC1 & _).
    pose proof (tape_read _ (ae_TAPE E) (ae_tws E) i TAPEB1 ltac:(lia)) as RDT1.
    pose proof (tape_read_typeX m1 (ae_TAPE E) (ae_tws E) i TAPEB1 ltac:(lia) TIR) as RDB1.
    shz_pose SHZN node. shz_pose SHZN (node + 8). shz_pose SHZD (ae_DOC E). shz_pose SHZT (ae_TAPE E + 8 * i).
    pose proof (SHZT m1 MU WM) as SHZT1.
    clear AI.
    lazymatch goal with H : rw_cells asegs m1 (q + -32) _ |- _ => rename H into FR1 end.
    destruct (Z.eq_dec (ttype (ae_T E i)) 91) as [T91|T91].
    2: { runX. atix_set_done MU WM FR1. }
    destruct (elem_view_of (ae_T E) (ae_S E) (ae_sn E) ck_any (fun c cv H => H) HSN d i j EL I0 ltac:(lia))
      as [TY Ej|TY Ej|TY Ej STR|d' e c Ed TY Ej NXT CLOSE TILES|d' e c Ed TY Ej NXT CLOSE TILES];
      unfold ty in TY; cbv [t_true t_false t_null t_i64 t_u64 t_dbl t_str t_arr t_obj] in TY; try (exfalso; lia).
    pose proof (tiles_le _ (elem_lt _ _ _ _ d') _ _ _ TILES) as [IE CC].
    destruct (Z.eq_dec (i + 1) e) as [IE1|IE1].
    { runX. atix_set_done MU WM FR1. }
    runtoX 0xb3a20.
    assert (XN : forall (y12 y13 y16 y28 y29 y30 y31 : word),
      evt asegs (atix_x1 q out ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m jo)
        (MS (mkR ra (wz (q + -32)) gp (wz TPV) (wz 4294967295) (wz 67240448) (wz 4294967297) s0 (wz 2147450880)
                 (wz out) (wz (ae_DOC E)) y12 y13 (wz (ae_TAPE E)) (wz e) y16 (wz 32)
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31) F (wz 0xb39c0) fc None m1 (seg_rom asegs))).
    { intros. runX. atix_set_done MU WM FR1. }
    assert (XF : forall (it : Z) (y12 y16 y28 y29 y30 y31 : word), 0 <= it < e ->
      evt asegs (atix_x1 q out ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m jo)
        (MS (mkR ra (wz (q + -32)) gp (wz TPV) (wz 4294967295) (wz 67240448) (wz 4294967297) s0 (wz 2147450880)
                 (wz out) (wz (ae_DOC E)) y12 (wz it) (wz (ae_TAPE E)) (wz e) y16 (wz 32)
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31) F (wz 0xb3a8c) fc None m1 (seg_rom asegs))).
    { intros it y12 y16 y28 y29 y30 y31 ITR.
      eapply (atix_found _ m1 F fc it q out ra s0 s1); [exact FR1| eassumption| eassumption| eassumption| lia| lia| lia| exact O8| exact Q16| lia| |].
      - intros m' MU' WM'.
        exact (SHZO m' (munch_trans _ _ _ _ MU (munch_weaken _ _ _ _ (sub_fp_atixW q out) MU')) (wmono_trans asegs _ _ _ WM WM')).
      - intros m' jo' y5 y6 y7 y10 y11 z12 y13 y14 y15 z16 y17 z28 z29 z30 z31 MU' WM' MI' ST' OUT'.
        right. exists m', jo'. do 15 eexists.
        split; [exact (munch_trans _ _ _ _ MU (munch_weaken _ _ _ _ (sub_fp_atixW q out) MU'))|].
        split; [exact (wmono_trans asegs _ _ _ WM WM')|]. split; [exact MI'|]. split; [exact OUT'|].
        split; [exact ST'| reflexivity]. }
    eapply evt_eq; [| eapply (atix_loop _ m1 F fc d' e q out ra gp s0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 AI1 SHZT1 ltac:(lia) XF XN
                               (S (Z.to_nat (e - (i + 1)))) (i + 1) c)];
      [atp_st_eq| exact TILES| lia| lia| lia].
  Qed.

End AtIxW.
