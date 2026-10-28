(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCt.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame Cells Step Mem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtMallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim STree Malloc Monad Stdio Prog LibProg ProgG.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import ApBase ApState ApInv ApErr ApParse ApPrim ApBridge.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtU Require Import Layout Lib_iface Lib_kit Printf_lib.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtHXU Require Import HxpFacts HxpInit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtBnU Require Import BnKit BnHeap BnRep W_crypto.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApCells ApRepDefs ApRep ApIface ApWalkTac ApErrKit ApErrKit2 W_err_new W_err_set_debug W_err_set_error W_get_object W_get_object_walk.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApUTac.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac step := ub; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.step.
Local Ltac zstep := ub; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep.

Ltac cell_of_bytes bs ::=
  lazymatch bs with
  | le8 ?v => constr:(C8 v)
  | le4 ?v => constr:(C4 v)
  | le2 ?v => constr:(C2 v)
  | [?b] => constr:(C1 b)
  | le1 (zxb ?b) => constr:(C1 b)
  | le1 (Z_to_bv 64 ?z) => constr:(C1 (Z_to_bv 8 z))
  | Z_to_le_bytes 8 ?z => constr:(C8 (Z_to_bv 64 z))
  | Z_to_le_bytes 4 ?z => constr:(C4 (Z_to_bv 64 z))
  | Z_to_le_bytes 1 ?z => constr:(C1 (Z_to_bv 8 z))
  end.

(* [comment removed for export] *)
Ltac zc H := rewrite ?bv_lts_zero_r, ?bv_lts_zero_l in H; unfold bv_eqb, bv_ltu, bv_lts, bv_leu in H; fold_lit_ux_in H; try zsimp_in H; zify_bool H.

Ltac to_implM :=
  lazymatch goal with |- impl ?segs _ (?c ?stt) (epost ?EE) ?ms =>
    lazymatch EE with (fun p => ?Q (fst p) (snd p)) => change (implM segs c stt Q ms) end end.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition C2I_IBUF : Z := 0x11464c.
(* [comment removed for export] *)
Definition C2I_IBUF_STACK : Z := 32 + ERR_SET_ERROR_STACK.
(* [comment removed for export] *)
Definition A_A_INT_C : Z := 0x22d86.
Definition A_C2I_IBUF : Z := 0x171fc.
Definition S_A_INT_C : list Z := [99; 114; 121; 112; 116; 111; 47; 97; 115; 110; 49; 47; 97; 95; 105; 110; 116; 46; 99].
Definition K_A_INT_C : list Z := [114; 115; 97; 95; 110; 101; 119].
Definition S_C2I_IBUF : list Z := [99; 50; 105; 95; 105; 98; 117; 102].
Definition K_C2I_IBUF : list Z := [65; 83; 78; 49; 95; 73; 78].

Local Ltac litc a s k :=
  unfold lit_ok, zb; rewrite !length_map;
  split; [vm_compute; reflexivity|];
  split; [cbv; intros HH; repeat (destruct HH as [HH|HH]; [apply (f_equal bv_unsigned) in HH; discriminate HH|]); exact HH|];
  split; [cbv; discriminate|]; unfold a; cbn; lia.

Lemma lit_a_int_c : lit_ok A_A_INT_C (zb S_A_INT_C) (zb K_A_INT_C) 20. Proof. litc A_A_INT_C S_A_INT_C K_A_INT_C. Qed.
Lemma lit_c2i_ibuf : lit_ok A_C2I_IBUF (zb S_C2I_IBUF) (zb K_C2I_IBUF) 9. Proof. litc A_C2I_IBUF S_C2I_IBUF K_C2I_IBUF. Qed.

(* [comment removed for export] *)
Definition acibuf (d : list Z) (cont plen : Z) : @AM bptr unit :=
  match c2i_ibuf_len d cont plen with
  | IbZero => err_raise RS_zero_content
  | IbPad => err_raise RS_ill_padding
  | IbOk _ => aret tt
  end.
Definition ibuf_val (r : ibuf_res) : Z := match r with IbOk n => n | _ => 0 end.

Lemma ibuf_val_range : forall d cont plen, 0 <= plen -> 0 <= ibuf_val (c2i_ibuf_len d cont plen) <= plen.
Proof.
  intros d cont plen Hp. unfold c2i_ibuf_len.
  destruct (Z.eqb_spec plen 0); [cbn; lia|]. destruct (Z.eqb_spec plen 1); [cbn; lia|].
  set (pad := if znth d cont =? 0 then 1 else _).
  assert (HP : 0 <= pad <= 1) by (subst pad; destruct (znth d cont =? 0); [lia|]; destruct (znth d cont =? 255); [|lia]; destruct (forallb _ _); lia).
  destruct (negb (pad =? 0) && _); cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma zeros_iff : forall d c n, 0 <= c -> 0 <= n -> c + n <= zlength d ->
  forallb (fun b => b =? 0) (firstn (Z.to_nat n) (skipn (Z.to_nat c) d)) = true <-> (forall k, 0 <= k < n -> znth d (c + k) = 0).
Proof.
  intros d c n Hc Hn Hcn. unfold zlength in Hcn. rewrite forallb_forall. split.
  - intros H k Hk. unfold znth. destruct (Z.ltb_spec (c + k) 0); [lia|].
    destruct (nth_error d (Z.to_nat (c + k))) as [x|] eqn:E.
    + rewrite (nth_error_nth _ _ _ E). apply Z.eqb_eq. apply H. apply In_iff_nth_error. exists (Z.to_nat k).
      rewrite nth_error_firstn. destruct (Nat.ltb_spec (Z.to_nat k) (Z.to_nat n)); [|lia]. rewrite nth_error_skipn. rewrite <- E. f_equal. lia.
    + apply nth_error_None in E. lia.
  - intros H x Hx. apply In_iff_nth_error in Hx. destruct Hx as [i Hi]. rewrite nth_error_firstn in Hi.
    destruct (Nat.ltb_spec i (Z.to_nat n)); [|discriminate]. rewrite nth_error_skipn in Hi.
    specialize (H (Z.of_nat i) ltac:(lia)). unfold znth in H. destruct (Z.ltb_spec (c + Z.of_nat i) 0); [lia|].
    replace (Z.to_nat (c + Z.of_nat i)) with (Z.to_nat c + i)%nat in H by lia. rewrite (nth_error_nth _ _ _ Hi) in H. apply Z.eqb_eq. exact H.
Qed.

Lemma lor_byte : forall a b, 0 <= a < 256 -> 0 <= b < 256 -> 0 <= Z.lor a b < 256.
Proof.
  intros a b Ha Hb. split; [apply Z.lor_nonneg; lia|].
  destruct (Z.eq_dec a 0) as [->|Na]; [rewrite Z.lor_0_l; lia|]. destruct (Z.eq_dec b 0) as [->|Nb]; [rewrite Z.lor_0_r; lia|].
  assert (NZ : Z.lor a b <> 0) by (intros HZ; apply Z.lor_eq_0_iff in HZ; lia).
  apply (Z.log2_lt_pow2 (Z.lor a b) 8); [pose proof (Z.lor_nonneg a b); lia|].
  rewrite Z.log2_lor by lia. apply Z.max_lub_lt; apply Z.log2_lt_pow2; lia.
Qed.

Lemma lor_zero_iff : forall a b, 0 <= a -> 0 <= b -> (Z.lor a b = 0 <-> a = 0 /\ b = 0).
Proof. intros a b Ha Hb. split; [apply Z.lor_eq_0_iff| intros [-> ->]; reflexivity]. Qed.

(* [comment removed for export] *)
Definition ibuf_post (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
    (s : PState) (OW LB : list block) (E : ap_env) (bo : Z * Z) (lo B : Z) (canary : word) (m : mem) (K : list block)
    (res : ibuf_res) (r : unit * ap_st bptr) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (F' : bvmap 5 word) (fc' : bv 32) m' OW' (errv' : word),
    ms' = MS (mkR ra sp gp (wz RATP) t0 t1 t2 s0 s1 (wz (ibuf_val res)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom ctusegs)
    /\ frm0 fc' /\ (forall k : reg, bv_unsigned k <> 10 -> reg_get F' k = reg_get F k)
    /\ ap_pre s' (snd r) m' OW' LB E bo sp lo B errv' canary 0
    /\ lx_pres LB (bv_unsigned sp) LIBW_AP m m'
    /\ ps_so s' = ps_so s /\ ps_fa s' = ps_fa s
    /\ blocks_kept K (snd r) OW' m m'.

(* [comment removed for export] *)
Definition c2i_ibuf_spec : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (st : ap_st bptr) (OW LB : list block) (E : ap_env) (bo : Z * Z)
         (lo B : Z) (errv canary : word) (K : list block)
         (D : Z) (d : list Z) (cont plen : Z),
    ap_pre s st m OW LB E bo sp lo B errv canary C2I_IBUF_STACK -> tp = wz RATP -> frm0 fc ->
    (forall b, In b K -> In b OW) -> (forall b, In b K -> ~ In (blk_id b) (es_ids st ++ env_ids E)) ->
    payload_ok m LB D d -> 0 < zlength d -> 0 <= cont -> 0 <= plen < 2^31 -> cont + plen <= zlength d ->
    a0 = wz 0 -> a1 = wz 0 -> a2 = wz (D + cont) -> a3 = wz plen ->
    implM ctusegs (interp (ap_embed (acibuf d cont plen st))) s
          (ibuf_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F s OW LB E bo lo B canary m K (c2i_ibuf_len d cont plen))
          (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (wz C2I_IBUF) fc None m (seg_rom ctusegs)).

Section Proofs.
  Hypothesis HM : rmalloc_stmt.
  Hypothesis HF : rfree_stmt.

  Section Act.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (m : mem) (s : PState) (st : ap_st bptr) (OW LB : list block) (E : ap_env) (bo : Z * Z) (lo B : Z) (errv canary : word) (K : list block).
  Variables (D : Z) (d : list Z) (cont plen : Z).
  Hypothesis PRE : ap_pre s st m OW LB E bo sp lo B errv canary C2I_IBUF_STACK.
  Hypothesis TP : tp = wz RATP.
  Hypothesis FRM : frm0 fc.
  Hypothesis KOW : forall b, In b K -> In b OW.
  Hypothesis KIDS : forall b, In b K -> ~ In (blk_id b) (es_ids st ++ env_ids E).
  Hypothesis PAY : payload_ok m LB D d.
  Hypothesis DNE : 0 < zlength d.
  Hypothesis CT0 : 0 <= cont.
  Hypothesis PL0 : 0 <= plen < 2^31.
  Hypothesis CPL : cont + plen <= zlength d.

  Local Notation W0 := ([(bv_unsigned sp - C2I_IBUF_STACK, bv_unsigned sp)]%Z) (only parsing).
  Definition ib_frame : list cell := [C8 s1; C8 s0; C8 ra].

  (* [comment removed for export] *)
  Definition ib_inv (m1 : mem) : Prop :=
    munch W0 m m1 /\ wmono ctusegs m m1 /\ mem_inv ctusegs m1 /\ stk ctusegs m1 lo (bv_unsigned sp + -32)
    /\ (exists jk, rw_cells ctusegs m1 (bv_unsigned sp + -32) (CB 8 jk :: ib_frame))
    /\ bytes_at ctusegs m1 D (to_bytes d) /\ rw_cells ctusegs m1 3355012 [C4 errv].

  Lemma ctx_facts :
    Forall (fun c => 0 <= c < 256) d /\ 0 < D /\ D + zlength d < 2 ^ 63 /\ zlength d < 2 ^ 30 /\ D + zlength d <= alloc_ceiling
    /\ alloc_ceiling <= lo /\ 3493888 <= lo /\ lo <= bv_unsigned sp - C2I_IBUF_STACK /\ bv_unsigned sp <= B /\ B < 2 ^ 63 /\ 0 <= bv_unsigned sp < 2 ^ 64
    /\ Z.of_nat (length (to_bytes d)) = zlength d.
  Proof using CPL DNE PAY PL0 PRE.
    destruct PRE as (HEAP & AS & IDS & DC & AUX & SPB & B63 & ST & CEIL & GLO & LO & ERR & SSP & MI & SP16).
    destruct PAY as (_ & HF' & D0 & D63 & D30 & HB).
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    assert (DC' : D + zlength d <= alloc_ceiling).
    { destruct HB as [->|(blk & HBLK & BL1 & BL2)]; [exfalso; revert DNE; cbn; unfold zlength; cbn; lia|].
      pose proof (LH_block_range _ _ _ _ HEAP ltac:(apply in_app_iff; right; exact HBLK)) as (BB0 & BB1 & BB2 & BB3 & BB4). lia. }
    unfold GLOBALS_TOP in *.
    repeat (split; [first [assumption|lia]|]). apply zlength_to_bytes.
  Qed.

  Local Ltac ib_unpack GI := destruct GI as (MU & WM & MI & ST & (jk & FR) & HB & ERR); unfold ib_frame in FR.
  Local Ltac ctx := pose proof ctx_facts as (DF & D0 & D63 & D30 & DCEIL & CEIL & GLO & LO & SPB & B63 & SPR & DLEN);
                   unfold C2I_IBUF_STACK, ERR_SET_ERROR_STACK in LO.

  (* [comment removed for export] *)
  Lemma pre_at_call : forall m2, ib_inv m2 ->
    ap_pre s st m2 OW LB E bo (Z_to_bv 64 (bv_unsigned sp + -32)) lo B errv canary ERR_SET_ERROR_STACK
    /\ lx_pres LB (bv_unsigned sp) LIBW_AP m m2
    /\ kept K m m2.
  Proof using CPL DNE KOW PAY PL0 PRE.
    intros m2 GI. ib_unpack GI. ctx.
    destruct PRE as (HEAP & AS & IDS & DC & AUX & SPB' & B63' & ST0 & CEIL' & GLO' & LO' & ERR0 & SSP & MI0 & SP16).
    assert (EA : errno_addr (Z_to_bv 64 RATP) = 3355012) by (unfold errno_addr, RATP; rewrite unsigned_lit by lia; reflexivity).
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -32)) = bv_unsigned sp + -32) by (apply unsigned_lit; lia).
    assert (INCL : forall b, In b OW -> In b (OW ++ LB)) by (intros b Hb; apply in_app_iff; left; exact Hb).
    pose proof (ap_state_es _ _ _ _ _ AS) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & OD).
    assert (HW : Forall (fun iv : Z * Z => lo <= fst iv /\ snd iv <= B) W0) by (unfold C2I_IBUF_STACK, ERR_SET_ERROR_STACK; repeat constructor; cbn; lia).
    unfold C2I_IBUF_STACK, ERR_SET_ERROR_STACK in MU.
    split; [|split].
    - unfold ap_pre. rewrite ESP. split.
      { eapply LH_frame; [exact HEAP|exact MU|exact WM|]. eapply Forall_impl; [|exact HW]. intros [x y] [Hx Hy]. apply W_ok_stack. cbn in *. lia. }
      split. { eapply (ap_state_of_munch st m m2); [exact AS|exact HEAP|exact INCL|exact MU|exact WM|exact CEIL|unfold GLOBALS_TOP; exact GLO|].
               eapply Forall_impl; [|exact HW]. intros iv [Hx Hy]. left. exact Hx. }
      split; [exact IDS|].
      split. { eapply (data_cells_of_munch s (OW ++ LB) _ m m2); [exact DC|intros i q k Hd; apply INCL; exact (proj1 (optb_ok_nth OW _ i q k OD Hd))|exact HEAP|exact CEIL|exact MU|exact WM|].
               eapply Forall_impl; [|exact HW]. intros iv [Hx Hy]. left. exact Hx. }
      split. { eapply rauxv_ok_frame; [exact AUX|exact MU|exact WM|]. eapply Forall_impl; [|exact HW]. intros [x y] [Hx Hy]. cbn in *. unfold RAUXV_CELL, GLOBALS_TOP in *. lia. }
      split; [lia|]. split; [lia|]. split; [exact ST|]. split; [exact CEIL|]. split; [unfold GLOBALS_TOP; lia|]. split; [unfold ERR_SET_ERROR_STACK; lia|].
      split; [unfold MallocRep.wz; rewrite EA; exact ERR|]. split; [rewrite (ssp_canary_0 _ _ _ _ HEAP SSP); eapply RHEAP_ssp; eapply LH_frame; [exact HEAP|exact MU|exact WM|]; eapply Forall_impl; [|exact HW]; intros [x y] [Hx Hy]; apply W_ok_stack; cbn in *; lia|].
      split; [exact MI|]. replace (bv_unsigned sp + -32) with (bv_unsigned sp - 32) by lia. rewrite Zminus_mod, SP16. reflexivity.
    - eapply lx_pres_of_munch; [exact MU|exact WM|]. intros a Ha [HX Hc]. cbn [rin_ivs fst snd app] in HX. cbn.
      destruct Hc as [Hc|[(b & Hb & Hr)|Hc]].
      + repeat split; try lia; tauto.
      + destruct b as [[q A] n]. cbn [blk_addr blk_size fst snd] in Hr.
        pose proof (blk_bounds _ _ _ q A n HEAP ltac:(apply in_app_iff; right; exact Hb)). repeat split; lia.
      + unfold ralloc_static in Hc. repeat split; lia.
    - eapply (kept_of_munch s (OW ++ LB) _ m m2 K lo); [exact HEAP|intros b Hb; apply INCL; apply KOW; exact Hb|exact CEIL|exact MU|].
      eapply Forall_impl; [|exact HW]. intros iv [Hx Hy]. left. exact Hx.
  Qed.

  (* [comment removed for export] *)
  Definition site_ok (base line reason : Z) (rs : rsite) : Prop :=
    (base = 0x1146a0 /\ line = 160 /\ reason = 222 /\ rs = RS_zero_content) \/ (base = 0x114738 /\ line = 193 /\ reason = 221 /\ rs = RS_ill_padding).

  (* [comment removed for export] *)
  Definition raise_post (x9 : word) (m2 : mem) (r : unit * ap_st bptr) (s' : PState) : machine_state -> Prop :=
    fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32) m' OW' (errv' : word),
      ms' = MS (mkR (Z_to_bv 64 0x1146cc) (Z_to_bv 64 (bv_unsigned sp + -32)) gp (wz RATP) t0 t1 t2 sp x9 a0 a1 a2 a3 a4 a5 a6 a7
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4' t5' t6')
               F' (Z_to_bv 64 0x1146cc) fc' None m' (seg_rom ctusegs)
      /\ frm0 fc' /\ (forall k : reg, bv_unsigned k <> 10 -> reg_get F' k = reg_get F k)
      /\ ap_pre s' (snd r) m' OW' LB E bo (Z_to_bv 64 (bv_unsigned sp + -32)) lo B errv' canary 0
      /\ lx_pres LB (bv_unsigned sp + -32) LIBW_AP m2 m'
      /\ ps_so s' = ps_so s /\ ps_fa s' = ps_fa s
      /\ blocks_kept K (snd r) OW' m m'.

  Lemma raise_seq : forall base line reason rs (x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x28 : word) m2,
    site_ok base line reason rs -> ib_inv m2 ->
    implM ctusegs (interp (ap_embed (err_raise rs st))) s (raise_post x9 m2)
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp x5 x6 x7 sp x9 x10 x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 t4 t5 t6)
          F (Z_to_bv 64 base) fc None m2 (seg_rom ctusegs)).
  Proof using CPL DNE FRM HF HM KIDS KOW PAY PL0 PRE TP.
    intros until m2. intros SITE GI.
    destruct (pre_at_call m2 GI) as (PRE2 & LX2 & KP2).
    ib_unpack GI. ctx. subst tp.
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -32)) = bv_unsigned sp + -32) by (apply unsigned_lit; lia).
    pose proof lit_a_int_c as LF. pose proof lit_c2i_ibuf as LN.
    unfold err_raise.
    destruct SITE as [(-> & -> & -> & ->)|(-> & -> & -> & ->)].
    - unfold implM. iprefix. step.
      ihere. to_implM.
      eapply implM_abind.
      { pose proof (ERR_new_walk HF bo) as W. unfold ap_stmt in W. eapply W; [eapply ap_pre_stack_le; [exact PRE2|unfold ERR_NEW_STACK, ERR_SET_ERROR_STACK; lia]|reflexivity|exact FRM|reflexivity|exact KOW|exact KIDS]. }
      intros r1 sA ms1 PO1. cbv beta in PO1.
      destruct PO1 as (q0 & q1 & q2 & q10 & q11 & q12 & q13 & q14 & q15 & q16 & q17 & q3 & q4 & q5 & q6 & F1 & fc1 & mA & OW1 & errv1 & bo1
                       & -> & FRM1 & FE1 & PREa & LXa & SOa & FAa & BKa & EBO1).
      subst bo1. replace (ret_pc (Z_to_bv 64 (1132192 + 4))) with (Z_to_bv 64 1132196) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      assert (KIDS1 : forall b, In b K -> ~ In (blk_id b) (es_ids (snd r1) ++ env_ids E)).
      { intros b Hb Hin. apply in_app_iff in Hin. destruct Hin as [Hin|Hin]; [exact (proj1 (proj2 BKa) b Hb Hin)|]. apply (KIDS b Hb). apply in_app_iff. right. exact Hin. }
      unfold implM. iprefix. do 6 step.
      ihere. to_implM.
      eapply implM_abind.
      { pose proof (ERR_set_debug_walk HM HF RS_zero_content A_A_INT_C A_C2I_IBUF bo _ _ _ _ LF LN) as W. unfold ap_stmt in W.
        eapply W; [eapply ap_pre_restack; [exact PREa|rewrite ESP; unfold ERR_SET_DEBUG_STACK; lia]|reflexivity|exact FRM1|cbn; unfold A_A_INT_C, A_C2I_IBUF, MallocRep.wz; repeat split; reflexivity|exact (proj1 BKa)|exact KIDS1]. }
      intros r2 sB ms2 PO2. cbv beta in PO2.
      destruct PO2 as (p0 & p1' & p2' & p10 & p11 & p12 & p13 & p14 & p15 & p16 & p17 & p3 & p4 & p5 & p6 & F2 & fc2 & mB & OW2 & errv2 & bo2
                       & -> & FRM2 & FE2 & PREb & LXb & SOb & FAb & BKb & EBO2).
      subst bo2.
      replace (ret_pc (Z_to_bv 64 (1132216 + 4))) with (Z_to_bv 64 1132220) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      assert (KIDS2 : forall b, In b K -> ~ In (blk_id b) (es_ids (snd r2) ++ env_ids E)).
      { intros b Hb Hin. apply in_app_iff in Hin. destruct Hin as [Hin|Hin]; [exact (proj1 (proj2 BKb) b Hb Hin)|]. apply (KIDS b Hb). apply in_app_iff. right. exact Hin. }
      unfold implM. iprefix. do 4 step.
      ihere. to_implM.
      eapply implM_mono.
      { pose proof (ERR_set_error_walk RS_zero_content 13 222 bo) as W. unfold ap_stmt in W.
        eapply W; [eapply ap_pre_restack; [exact PREb|rewrite ESP; unfold ERR_SET_ERROR_STACK; lia]|reflexivity|exact FRM2| |exact (proj1 BKb)|exact KIDS2].
        cbn. unfold ERR_LIB_SYS, MallocRep.wz. repeat split; try reflexivity; lia. }
      intros r3 sC ms3 PO3. cbv beta in PO3.
      destruct PO3 as (o0 & o1 & o2 & o10 & o11 & o12 & o13 & o14 & o15 & o16 & o17 & o3 & o4 & o5 & o6 & F3 & fc3 & mC & OW3 & errv3 & bo3
                       & -> & FRM3 & FE3 & PREc & LXc & SOc & FAc & BKc & EBO3). subst bo3.
      replace (ret_pc (Z_to_bv 64 (1132232 + 4))) with (Z_to_bv 64 1132236) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      unfold raise_post. exists o0, o1, o2, o10, o11, o12, o13, o14, o15, o16, o17, o3, o4, o5, o6, F3, fc3, mC, OW3, errv3.
      split; [reflexivity|]. split; [exact FRM3|]. split; [intros k Hk; rewrite (FE3 k Hk), (FE2 k Hk); apply (FE1 k Hk)|].
      split; [exact PREc|]. split; [rewrite <- ESP; eapply lx_pres_trans; [exact LXa|eapply lx_pres_trans; [exact LXb|exact LXc]]|].
      split; [rewrite SOc, SOb; exact SOa|]. split; [rewrite FAc, FAb; exact FAa|].
      split; [exact (proj1 BKc)|]. split; [exact (proj1 (proj2 BKc))|].
      eapply kept_trans; [exact KP2|]. eapply kept_trans; [exact (proj2 (proj2 BKa))|]. eapply kept_trans; [exact (proj2 (proj2 BKb))|exact (proj2 (proj2 BKc))].
    - unfold implM. iprefix. step.
      ihere. to_implM.
      eapply implM_abind.
      { pose proof (ERR_new_walk HF bo) as W. unfold ap_stmt in W. eapply W; [eapply ap_pre_stack_le; [exact PRE2|unfold ERR_NEW_STACK, ERR_SET_ERROR_STACK; lia]|reflexivity|exact FRM|reflexivity|exact KOW|exact KIDS]. }
      intros r1 sA ms1 PO1. cbv beta in PO1.
      destruct PO1 as (q0 & q1 & q2 & q10 & q11 & q12 & q13 & q14 & q15 & q16 & q17 & q3 & q4 & q5 & q6 & F1 & fc1 & mA & OW1 & errv1 & bo1
                       & -> & FRM1 & FE1 & PREa & LXa & SOa & FAa & BKa & EBO1).
      subst bo1. replace (ret_pc (Z_to_bv 64 (1132344 + 4))) with (Z_to_bv 64 1132348) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      assert (KIDS1 : forall b, In b K -> ~ In (blk_id b) (es_ids (snd r1) ++ env_ids E)).
      { intros b Hb Hin. apply in_app_iff in Hin. destruct Hin as [Hin|Hin]; [exact (proj1 (proj2 BKa) b Hb Hin)|]. apply (KIDS b Hb). apply in_app_iff. right. exact Hin. }
      unfold implM. iprefix. do 6 step.
      ihere. to_implM.
      eapply implM_abind.
      { pose proof (ERR_set_debug_walk HM HF RS_ill_padding A_A_INT_C A_C2I_IBUF bo _ _ _ _ LF LN) as W. unfold ap_stmt in W.
        eapply W; [eapply ap_pre_restack; [exact PREa|rewrite ESP; unfold ERR_SET_DEBUG_STACK; lia]|reflexivity|exact FRM1|cbn; unfold A_A_INT_C, A_C2I_IBUF, MallocRep.wz; repeat split; reflexivity|exact (proj1 BKa)|exact KIDS1]. }
      intros r2 sB ms2 PO2. cbv beta in PO2.
      destruct PO2 as (p0 & p1' & p2' & p10 & p11 & p12 & p13 & p14 & p15 & p16 & p17 & p3 & p4 & p5 & p6 & F2 & fc2 & mB & OW2 & errv2 & bo2
                       & -> & FRM2 & FE2 & PREb & LXb & SOb & FAb & BKb & EBO2).
      subst bo2.
      replace (ret_pc (Z_to_bv 64 (1132368 + 4))) with (Z_to_bv 64 1132372) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      assert (KIDS2 : forall b, In b K -> ~ In (blk_id b) (es_ids (snd r2) ++ env_ids E)).
      { intros b Hb Hin. apply in_app_iff in Hin. destruct Hin as [Hin|Hin]; [exact (proj1 (proj2 BKb) b Hb Hin)|]. apply (KIDS b Hb). apply in_app_iff. right. exact Hin. }
      unfold implM. iprefix. do 5 step.
      ihere. to_implM.
      eapply implM_mono.
      { pose proof (ERR_set_error_walk RS_ill_padding 13 221 bo) as W. unfold ap_stmt in W.
        eapply W; [eapply ap_pre_restack; [exact PREb|rewrite ESP; unfold ERR_SET_ERROR_STACK; lia]|reflexivity|exact FRM2| |exact (proj1 BKb)|exact KIDS2].
        cbn. unfold ERR_LIB_SYS, MallocRep.wz. repeat split; try reflexivity; lia. }
      intros r3 sC ms3 PO3. cbv beta in PO3.
      destruct PO3 as (o0 & o1 & o2 & o10 & o11 & o12 & o13 & o14 & o15 & o16 & o17 & o3 & o4 & o5 & o6 & F3 & fc3 & mC & OW3 & errv3 & bo3
                       & -> & FRM3 & FE3 & PREc & LXc & SOc & FAc & BKc & EBO3). subst bo3.
      replace (ret_pc (Z_to_bv 64 (1132232 + 4))) with (Z_to_bv 64 1132236) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      unfold raise_post. exists o0, o1, o2, o10, o11, o12, o13, o14, o15, o16, o17, o3, o4, o5, o6, F3, fc3, mC, OW3, errv3.
      split; [reflexivity|]. split; [exact FRM3|]. split; [intros k Hk; rewrite (FE3 k Hk), (FE2 k Hk); apply (FE1 k Hk)|].
      split; [exact PREc|]. split; [rewrite <- ESP; eapply lx_pres_trans; [exact LXa|eapply lx_pres_trans; [exact LXb|exact LXc]]|].
      split; [rewrite SOc, SOb; exact SOa|]. split; [rewrite FAc, FAb; exact FAa|].
      split; [exact (proj1 BKc)|]. split; [exact (proj1 (proj2 BKc))|].
      eapply kept_trans; [exact KP2|]. eapply kept_trans; [exact (proj2 (proj2 BKa))|]. eapply kept_trans; [exact (proj2 (proj2 BKb))|exact (proj2 (proj2 BKc))].
  Qed.

  (* [comment removed for export] *)
  Lemma pre_at_ret : forall m2, munch W0 m m2 -> wmono ctusegs m m2 -> mem_inv ctusegs m2 -> stk ctusegs m2 lo (bv_unsigned sp) ->
    rw_cells ctusegs m2 3355012 [C4 errv] ->
    ap_pre s st m2 OW LB E bo sp lo B errv canary 0
    /\ lx_pres LB (bv_unsigned sp) LIBW_AP m m2
    /\ kept K m m2.
  Proof using CPL DNE KOW PAY PL0 PRE.
    intros m2 MU WM MI ST ERR. ctx.
    destruct PRE as (HEAP & AS & IDS & DC & AUX & SPB' & B63' & ST0 & CEIL' & GLO' & LO' & ERR0 & SSP & MI0 & SP16).
    assert (EA : errno_addr (Z_to_bv 64 RATP) = 3355012) by (unfold errno_addr, RATP; rewrite unsigned_lit by lia; reflexivity).
    assert (INCL : forall b, In b OW -> In b (OW ++ LB)) by (intros b Hb; apply in_app_iff; left; exact Hb).
    pose proof (ap_state_es _ _ _ _ _ AS) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & OD).
    unfold C2I_IBUF_STACK, ERR_SET_ERROR_STACK in MU.
    assert (HW : Forall (fun iv : Z * Z => lo <= fst iv /\ snd iv <= B) W0) by (unfold C2I_IBUF_STACK, ERR_SET_ERROR_STACK; repeat constructor; cbn; lia).
    unfold C2I_IBUF_STACK, ERR_SET_ERROR_STACK in HW.
    assert (HEAP2 : RHEAP s (OW ++ LB) m2).
    { eapply LH_frame; [exact HEAP|exact MU|exact WM|]. eapply Forall_impl; [|exact HW]. intros [x y] [Hx Hy]. apply W_ok_stack. cbn in *. lia. }
    split; [|split].
    - unfold ap_pre. split; [exact HEAP2|].
      split. { eapply (ap_state_of_munch st m m2); [exact AS|exact HEAP|exact INCL|exact MU|exact WM|exact CEIL|unfold GLOBALS_TOP; exact GLO|].
               eapply Forall_impl; [|exact HW]. intros iv [Hx Hy]. left. exact Hx. }
      split; [exact IDS|].
      split. { eapply (data_cells_of_munch s (OW ++ LB) _ m m2); [exact DC|intros i q k Hd; apply INCL; exact (proj1 (optb_ok_nth OW _ i q k OD Hd))|exact HEAP|exact CEIL|exact MU|exact WM|].
               eapply Forall_impl; [|exact HW]. intros iv [Hx Hy]. left. exact Hx. }
      split. { eapply rauxv_ok_frame; [exact AUX|exact MU|exact WM|]. eapply Forall_impl; [|exact HW]. intros [x y] [Hx Hy]. cbn in *. unfold RAUXV_CELL, GLOBALS_TOP in *. lia. }
      split; [lia|]. split; [lia|]. split; [exact ST|]. split; [exact CEIL|]. split; [unfold GLOBALS_TOP; lia|]. split; [lia|].
      split; [unfold MallocRep.wz; rewrite EA; exact ERR|]. split; [rewrite (ssp_canary_0 _ _ _ _ HEAP SSP); eapply RHEAP_ssp; exact HEAP2|].
      split; [exact MI|exact SP16].
    - eapply lx_pres_of_munch; [exact MU|exact WM|]. intros a Ha [HX Hc]. cbn [rin_ivs fst snd app] in HX. cbn.
      destruct Hc as [Hc|[(b & Hb & Hr)|Hc]].
      + repeat split; try lia; tauto.
      + destruct b as [[q A] n]. cbn [blk_addr blk_size fst snd] in Hr.
        pose proof (blk_bounds _ _ _ q A n HEAP ltac:(apply in_app_iff; right; exact Hb)). repeat split; lia.
      + unfold ralloc_static in Hc. repeat split; lia.
    - eapply (kept_of_munch s (OW ++ LB) _ m m2 K lo); [exact HEAP|intros b Hb; apply INCL; apply KOW; exact Hb|exact CEIL|exact MU|].
      eapply Forall_impl; [|exact HW]. intros iv [Hx Hy]. left. exact Hx.
  Qed.

  (* [comment removed for export] *)
  Lemma pre_resp : forall sF (st' : ap_st bptr) mX OW' (errv' : word),
    ap_pre sF st' mX OW' LB E bo (Z_to_bv 64 (bv_unsigned sp + -32)) lo B errv' canary 0 ->
    stk ctusegs mX lo (bv_unsigned sp) ->
    ap_pre sF st' mX OW' LB E bo sp lo B errv' canary 0.
  Proof using CPL DNE PAY PL0 PRE.
    intros until errv'. intros PREX ST4. ctx.
    destruct PREX as (HEAP & AS & IDS & DC & AUX & SPB' & B63' & ST0 & CEIL' & GLO' & LO' & ERR0 & SSP & MI0 & SP16).
    destruct PRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SP16e).
    unfold ap_pre. repeat (split; [first [assumption|lia]|]). exact SP16e.
  Qed.

  (* [comment removed for export] *)
  Lemma ibuf_ge2 : forall pad, 2 <= plen ->
    pad = (if znth d cont =? 0 then 1 else if znth d cont =? 255
           then (if forallb (fun b => b =? 0) (firstn (Z.to_nat (plen - 1)) (skipn (Z.to_nat (cont + 1)) d)) then 0 else 1) else 0) ->
    c2i_ibuf_len d cont plen = if negb (pad =? 0) && (Z.land (znth d cont) 128 =? Z.land (znth d (cont + 1)) 128) then IbPad else IbOk (plen - pad).
  Proof using PL0.
    intros pad H2 ->. unfold c2i_ibuf_len. rewrite (proj2 (Z.eqb_neq plen 0)) by lia. rewrite (proj2 (Z.eqb_neq plen 1)) by lia. reflexivity.
  Qed.

  Local Notation IBPOST := (ibuf_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F s OW LB E bo lo B canary m K (c2i_ibuf_len d cont plen)).
  Local Notation IPOST := (fun ms' : machine_state => impl ctusegs (at_node ctusegs) (interp (ap_embed (acibuf d cont plen st)) s)
                              (epost (fun p : unit * ap_st bptr * PState => IBPOST (fst p) (snd p))) ms').

  (* [comment removed for export] *)
  Lemma or_loop : forall fuel (i acc : Z) (x6 x7 x9 x10 x12 x13 x14 x15 x28 : word) m1 (POST : machine_state -> Prop),
    ib_inv m1 -> Z.to_nat (plen - i) = fuel -> 1 <= i < plen -> 0 <= acc < 256 ->
    (acc = 0 <-> forall k, 1 <= k < i -> znth d (cont + k) = 0) ->
    (forall acc' (x6' : word), 0 <= acc' < 256 ->
       (acc' = 0 <-> forall k, 1 <= k < plen -> znth d (cont + k) = 0) ->
       evt ctusegs POST
         (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp (Z_to_bv 64 (D + cont + plen)) x6' x7 sp x9 x10 (Z_to_bv 64 (D + cont + plen)) x12 x13 x14 x15
                  (Z_to_bv 64 acc') (Z_to_bv 64 (D + cont + plen)) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 t4 t5 t6)
             F (Z_to_bv 64 0x114720) fc None m1 (seg_rom ctusegs))) ->
    evt ctusegs POST
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp (Z_to_bv 64 (D + cont + i)) x6 x7 sp x9 x10 (Z_to_bv 64 (D + cont + i)) x12 x13 x14 x15
               (Z_to_bv 64 acc) (Z_to_bv 64 (D + cont + plen)) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 t4 t5 t6)
          F (Z_to_bv 64 0x114708) fc None m1 (seg_rom ctusegs)).
  Proof using CPL CT0 DNE PAY PL0 PRE.
    induction fuel as [|fuel IH]; intros i acc x6 x7 x9 x10 x12 x13 x14 x15 x28 m1 POST GI Hf Hi Hacc INVA KONT; [lia|].
    pose proof GI as GI'. ib_unpack GI. ctx.
    pose proof (znth_range d (cont + i) DF) as BR.
    pose proof (payload_read _ D d (cont + i) (wa (D + cont + i)) HB DF ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD. step. clear RD.
    rewrite (zxb_lit (znth d (cont + i))) by lia.
    step. step. step. rewrite ?(unsigned_lit (znth d (cont + i))) by lia. rewrite ?(unsigned_lit acc) by lia.
    pose proof (lor_byte acc (znth d (cont + i)) Hacc BR) as LB'.
    assert (INVB : Z.lor acc (znth d (cont + i)) = 0 <-> forall k, 1 <= k < i + 1 -> znth d (cont + k) = 0).
    { rewrite (lor_zero_iff acc (znth d (cont + i))) by lia. rewrite INVA. split.
      - intros [H1 H2] k Hk. destruct (Z.eq_dec k i) as [->|Hne]; [exact H2| apply H1; lia].
      - intros H1. split; [intros k Hk; apply H1; lia| apply H1; lia]. }
    step. if_cases KX; zc KX.
    - (* [comment removed for export] *)
      replace (D + cont + i + 1) with (D + cont + (i + 1)) by lia.
      eapply (IH (i + 1) (Z.lor acc (znth d (cont + i)))); [exact GI'| lia| lia| exact LB'| exact INVB| exact KONT].
    - (* [comment removed for export] *)
      assert (Ei : i + 1 = plen) by lia.
      replace (D + cont + i + 1) with (D + cont + plen) by lia.
      eapply KONT; [exact LB'|]. rewrite <- Ei. exact INVB.
  Qed.

  (* [comment removed for export] *)
  Lemma fin_ok : forall v (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 : word) m1,
    ib_inv m1 -> c2i_ibuf_len d cont plen = IbOk v -> 0 <= v < 2 ^ 63 ->
    evt ctusegs IPOST
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp x5 x6 x7 sp (Z_to_bv 64 v) x10 x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 t4 t5 t6)
          F (Z_to_bv 64 0x114794) fc None m1 (seg_rom ctusegs)).
  Proof using CPL DNE FRM KIDS KOW PAY PL0 PRE TP.
    intros until m1. intros GI EQ Hv. ib_unpack GI. ctx. subst tp.
    step. step. step. step. step. release_frame FR ST (bv_unsigned sp). step.
    apply evt_done. cbv beta. unfold acibuf. rewrite EQ. cbn [aret ap_embed interp impl]. apply evt_done. unfold epost. cbn [fst snd].
    destruct (pre_at_ret m1 MU WM MI ST ERR) as (PRE3 & LX3 & KP3).
    unfold ibuf_post. cbn [ibuf_val].
    eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, F, fc, m1, OW, errv.
    split; [unfold MallocRep.wz; reflexivity|]. split; [exact FRM|]. split; [intros; reflexivity|].
    split; [exact PRE3|]. split; [exact LX3|]. split; [reflexivity|]. split; [reflexivity|].
    split; [exact KOW|]. split; [intros b Hb Hin; apply (KIDS b Hb); apply in_app_iff; left; exact Hin| exact KP3].
  Qed.

  (* [comment removed for export] *)
  Lemma fin_raise : forall res x9 m2 (r : unit * ap_st bptr) sF msF,
    res = IbZero \/ res = IbPad -> ib_inv m2 ->
    raise_post x9 m2 r sF msF ->
    evt ctusegs (fun ms'' => ibuf_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F s OW LB E bo lo B canary m K res r sF ms'') msF.
  Proof using CPL DNE KOW PAY PL0 PRE.
    intros res x9 m2 r sF msF EQ GI RP. pose proof GI as GI'. ib_unpack GI. ctx. subst tp.
    unfold raise_post in RP.
    destruct RP as (w0 & w1 & w2 & w10 & w11 & w12 & w13 & w14 & w15 & w16 & w17 & w3 & w4 & w5 & w6 & FF & fcF & mF & OWF & errvF
                    & -> & FRMF & FEF & PREF & LXF & SOF & FAF & BKF).
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -32)) = bv_unsigned sp + -32) by (apply unsigned_lit; lia).
    pose proof PREF as (HEAPF & ASF & IDSF & DCF & AUXF & SPBF & B63F & STF & CEILF & GLOF & LOF & ERRF & SSPF & MIF & SP16F). rewrite ESP in STF.
    pose proof (agree_of_lx_pres _ _ _ _ _ LXF) as AGF.
    assert (CL : forall a, bv_unsigned sp + -32 <= a -> lx_client LB (bv_unsigned sp + -32) LIBW_AP a).
    { intros a Ha. split; [unfold LIBW_AP; cbn [rin_ivs fst snd]; lia|left; exact Ha]. }
    apply (rw_cells_agree _ _ _ _ _ AGF) in FR; [|intros a Ha; apply CL; cbn in Ha; lia].
    clear MU WM MI ST HB ERR.
    pose proof (munch_refl (@nil (Z * Z)) mF) as MU. pose proof (wmono_refl ctusegs mF) as WM.
    step. step. step. step. step. step. step. release_frame FR STF (bv_unsigned sp). step.
    apply evt_done.
    pose proof (pre_resp sF (snd r) mF OWF errvF PREF STF) as PRE4.
    unfold ibuf_post. replace (ibuf_val res) with 0 by (destruct EQ as [-> | ->]; reflexivity).
    eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, FF, fcF, mF, OWF, errvF.
    split; [unfold MallocRep.wz; reflexivity|]. split; [exact FRMF|]. split; [exact FEF|].
    split; [exact PRE4|].
    split. { eapply lx_pres_trans; [exact (proj1 (proj2 (pre_at_call _ GI')))|].
             eapply lx_pres_weaken; [exact LXF|lia|intros b Hb; exact Hb|]. intros a Ha. exact Ha. }
    split; [exact SOF|]. split; [exact FAF|]. exact BKF.
  Qed.

  (* [comment removed for export] *)
  Lemma pad_check : forall (x5 x6 x7 x9 x11 x16 x17 x28 : word) m1,
    ib_inv m1 -> 2 <= plen ->
    c2i_ibuf_len d cont plen = (if Z.land (znth d cont) 128 =? Z.land (znth d (cont + 1)) 128 then IbPad else IbOk (plen - 1)) ->
    evt ctusegs IPOST
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp x5 x6 x7 sp x9 (Z_to_bv 64 0) x11 (Z_to_bv 64 (D + cont)) (Z_to_bv 64 plen)
               (Z_to_bv 64 (znth d cont)) (Z_to_bv 64 (Z.land (znth d cont) 128)) x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 t4 t5 t6)
          F (Z_to_bv 64 0x114724) fc None m1 (seg_rom ctusegs)).
  Proof using CPL CT0 DNE FRM HF HM KIDS KOW PAY PL0 PRE TP.
    intros until m1. intros GI H2 EQ. pose proof GI as GI'. ib_unpack GI. ctx.
    pose proof (znth_range d cont DF) as B0R. pose proof (znth_range d (cont + 1) DF) as B1R.
    pose proof (land128_cases (znth d cont) B0R) as C0. pose proof (land128_cases (znth d (cont + 1)) B1R) as C1.
    pose proof (payload_read _ D d (cont + 1) (wa (D + cont + 1)) HB DF ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD. step. clear RD.
    rewrite (zxb_lit (znth d (cont + 1))) by lia.
    step. rewrite ?(unsigned_lit (znth d (cont + 1))) by lia.
    step. if_cases KP; zc KP.
    - (* [comment removed for export] *)
      rewrite (proj2 (Z.eqb_neq _ _)) in EQ by lia.
      step. step. rewrite ?unsigned_lit by lia.
      step. if_cases KB; zc KB; [| exfalso; apply KB; reflexivity].
      replace (-1 + plen) with (plen - 1) by lia.
      eapply fin_ok; [exact GI'| exact EQ| lia].
    - (* [comment removed for export] *)
      rewrite (proj2 (Z.eqb_eq _ _)) in EQ by lia.
      apply evt_done. cbv beta. unfold acibuf. rewrite EQ. to_implM.
      eapply implM_post_evt. eapply implM_mono; [eapply (raise_seq 0x114738 193 221 RS_ill_padding); [right; repeat split; reflexivity|exact GI']|].
      intros r sF msF RP. cbv beta. eapply (fin_raise IbPad); [right; reflexivity| exact GI'| exact RP].
  Qed.

  (* [comment removed for export] *)
  Theorem ib_main : forall (t0 t1 t2 t3 a4 a5 a6 a7 : word),
    implM ctusegs (interp (ap_embed (acibuf d cont plen st))) s IBPOST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz 0) (wz 0) (wz (D + cont)) (wz plen) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz C2I_IBUF) fc None m (seg_rom ctusegs)).
  Proof using CPL CT0 DNE FRM HF HM KIDS KOW PAY PL0 PRE TP.
    intros. unfold implM. iprefix.
    destruct PRE as (HEAP & AS & IDS & DC & AUX & SPB' & B63' & ST & CEIL' & GLO' & LO' & ERR & SSP & MI & SP16). ctx.
    destruct PAY as (HB & _).
    assert (EA : errno_addr (Z_to_bv 64 RATP) = 3355012) by (unfold errno_addr, RATP; rewrite unsigned_lit by lia; reflexivity).
    unfold MallocRep.wz in ERR. rewrite EA in ERR.
    unfold C2I_IBUF, MallocRep.wz.
    pose proof (munch_refl W0 m) as MU. pose proof (wmono_refl ctusegs m) as WM.
    unfold C2I_IBUF_STACK, ERR_SET_ERROR_STACK in MU.
    pose proof (znth_range d cont DF) as B0R.
    carve_frame 32%nat ST. do 5 step.
    name_mem m1.
    assert (GI : ib_inv m1).
    { split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|]. split; [eexists; exact FR|]. split; [exact HB|exact ERR]. }
    step. if_cases KZ; zc KZ.
    - (* [comment removed for export] *)
      assert (EQ0 : c2i_ibuf_len d cont plen = IbZero) by (unfold c2i_ibuf_len; rewrite (proj2 (Z.eqb_eq plen 0) KZ); reflexivity).
      apply evt_done. cbv beta. unfold acibuf. rewrite EQ0. to_implM.
      eapply implM_post_evt. eapply implM_mono; [eapply (raise_seq 0x1146a0 160 222 RS_zero_content); [left; repeat split; reflexivity|exact GI]|].
      intros r sF msF RP. cbv beta. eapply (fin_raise IbZero); [left; reflexivity| exact GI| exact RP].
    - (* [comment removed for export] *)
      pose proof (payload_read _ D d cont (wa (D + cont)) HB DF ltac:(lia) eq_refl) as RD. step. clear RD.
      rewrite (zxb_lit (znth d cont)) by lia.
      step. rewrite ?(unsigned_lit (znth d cont)) by lia.
      step. if_true. step. step. if_cases K1; zc K1.
      + (* [comment removed for export] *)
        pose proof (payload_read _ D d cont (wa (D + cont)) HB DF ltac:(lia) eq_refl) as RD. step. clear RD.
        rewrite (zxb_lit (znth d cont)) by lia.
        step. if_cases KB0; zc KB0.
        * (* [comment removed for export] *)
          eapply pad_check; [exact GI| lia|].
          apply (ibuf_ge2 1); [lia|]. rewrite (proj2 (Z.eqb_eq _ _) KB0). reflexivity.
        * step. step. if_cases KFF; zc KFF.
          -- (* [comment removed for export] *)
             step. step. step. step. if_true. rewrite ?unsigned_lit by lia.
             replace (0 + plen) with plen by lia.
             eapply (fin_ok plen); [exact GI| | lia].
             rewrite (ibuf_ge2 0); [cbn; f_equal; lia| lia|]. rewrite (proj2 (Z.eqb_neq _ _) KB0). rewrite (proj2 (Z.eqb_neq _ _) KFF). reflexivity.
          -- (* [comment removed for export] *)
             step. step. step. step. udecide. step. step. step. step. OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep.
             replace (D + cont + (plen + -2) + 2) with (D + cont + plen) by lia.
             eapply (or_loop (Z.to_nat (plen - 1)) 1 0); [exact GI| lia| lia| lia| split; [intros _ k Hk; lia| intros; reflexivity]|].
             intros acc' x6' Hacc' HINV.
             step. if_cases KA; zc KA.
             ++ (* [comment removed for export] *)
                step. step. step. step. if_true. rewrite ?unsigned_lit by lia.
                replace (0 + plen) with plen by lia.
                eapply (fin_ok plen); [exact GI| | lia].
                rewrite (ibuf_ge2 0); [cbn; f_equal; lia| lia|]. rewrite (proj2 (Z.eqb_neq _ _)) by lia. rewrite (proj2 (Z.eqb_eq _ _) KFF).
                rewrite (proj2 (zeros_iff d (cont + 1) (plen - 1) ltac:(lia) ltac:(lia) ltac:(lia))); [reflexivity|].
                intros k Hk. replace (cont + 1 + k) with (cont + (k + 1)) by lia. apply (proj1 HINV ltac:(lia)). lia.
             ++ (* [comment removed for export] *)
                eapply pad_check; [exact GI| lia|].
                apply (ibuf_ge2 1); [lia|]. rewrite (proj2 (Z.eqb_neq _ _)) by lia. rewrite (proj2 (Z.eqb_eq _ _) KFF).
                destruct (forallb _ _) eqn:FB; [|reflexivity]. exfalso. apply KA. apply (proj2 HINV).
                intros k Hk. replace (cont + k) with (cont + 1 + (k - 1)) by lia.
                apply (proj1 (zeros_iff d (cont + 1) (plen - 1) ltac:(lia) ltac:(lia) ltac:(lia)) FB). lia.
      + (* [comment removed for export] *)
        step. if_true.
        eapply (fin_ok 1); [exact GI| | lia].
        unfold c2i_ibuf_len. rewrite (proj2 (Z.eqb_neq plen 0)) by lia. rewrite (proj2 (Z.eqb_eq plen 1)) by lia. reflexivity.
  Qed.
  End Act.

  (* [comment removed for export] *)
  Theorem c2i_ibuf_walk : c2i_ibuf_spec.
  Proof using HF HM.
    unfold c2i_ibuf_spec. intros until plen. intros PRE TP FRM KOW KIDS PAY DNE CT0 PL0 CPL -> -> -> ->.
    eapply (ib_main ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 t6 F fc m s st OW LB E bo lo B errv canary K D d cont plen);
      assumption.
  Qed.
End Proofs.
End WithCeiling0.
