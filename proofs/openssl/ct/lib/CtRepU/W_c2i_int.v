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
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtU Require Import Layout Lib_iface Lib_kit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtHXU Require Import HxpFacts HxpInit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtBnU Require Import BnKit BnHeap BnRep W_crypto.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApCells ApRepDefs ApRep ApIface ApWalkTac ApErrKit ApErrKit2 W_prefix_create W_obj_free W_asn1_string W_get_object W_get_object_walk W_c2i_ibuf W_c2i_ibuf2.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApUTac.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtParseU Require Import PzDefs.
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

Ltac zc H := rewrite ?bv_lts_zero_r, ?bv_lts_zero_l in H; unfold bv_eqb, bv_ltu, bv_lts, bv_leu in H; fold_lit_ux_in H; try zsimp_in H; zify_bool H.

Ltac to_implM :=
  lazymatch goal with |- impl ?segs _ (?c ?stt) (epost ?EE) ?ms =>
    lazymatch EE with (fun p => ?Q (fst p) (snd p)) => change (implM segs c stt Q ms) end end.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

(* [comment removed for export] *)
Definition phid (P : Prop) : Prop := P.
Ltac phide H := lazymatch type of H with ?T => change T with (phid T) in H end.
Ltac punhide := unfold phid in *.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ap_pre_seg : forall s st m m' OW LB E bo (sp sp' : word) lo B errv errv' canary stack stack' W,
  ap_pre s st m OW LB E bo sp lo B errv canary stack ->
  munch W m m' -> wmono ctusegs m m' -> mem_inv ctusegs m' -> stk ctusegs m' lo (bv_unsigned sp') ->
  Forall (fun iv : Z * Z => lo <= fst iv /\ snd iv <= B) W ->
  lo <= bv_unsigned sp' - stack' -> bv_unsigned sp' <= B -> bv_unsigned sp' mod 16 = 0 ->
  rw_cells ctusegs m' 3355012 [C4 errv'] ->
  ap_pre s st m' OW LB E bo sp' lo B errv' canary stack'.
Proof.
  intros until W. intros PRE MU WM MI' ST' HW LO' SPB' SP16' ERR'.
  destruct PRE as (HEAP & AS & IDS & DC & AUX & SPB & B63 & ST & CEIL & GLO & LO & ERR & SSP & MI & SP16).
  assert (EA : errno_addr (Z_to_bv 64 RATP) = 3355012) by (unfold errno_addr, RATP; rewrite unsigned_lit by lia; reflexivity).
  assert (INCL : forall b, In b OW -> In b (OW ++ LB)) by (intros b Hb; apply in_app_iff; left; exact Hb).
  pose proof (ap_state_es _ _ _ _ _ AS) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & OD).
  assert (HEAP' : RHEAP s (OW ++ LB) m').
  { eapply LH_frame; [exact HEAP|exact MU|exact WM|]. eapply Forall_impl; [|exact HW]. intros [x y] [Hx Hy]. apply W_ok_stack. cbn in *. lia. }
  unfold ap_pre. split; [exact HEAP'|].
  split. { eapply (ap_state_of_munch st m m'); [exact AS|exact HEAP|exact INCL|exact MU|exact WM|exact CEIL|exact GLO|].
           eapply Forall_impl; [|exact HW]. intros iv [Hx Hy]. left. exact Hx. }
  split; [exact IDS|].
  split. { eapply (data_cells_of_munch s (OW ++ LB) _ m m'); [exact DC|intros i q k Hd; apply INCL; exact (proj1 (optb_ok_nth OW _ i q k OD Hd))|exact HEAP|exact CEIL|exact MU|exact WM|].
           eapply Forall_impl; [|exact HW]. intros iv [Hx Hy]. left. exact Hx. }
  split. { eapply rauxv_ok_frame; [exact AUX|exact MU|exact WM|]. eapply Forall_impl; [|exact HW]. intros [x y] [Hx Hy]. cbn in *. unfold RAUXV_CELL, GLOBALS_TOP in *. lia. }
  split; [lia|]. split; [lia|]. split; [exact ST'|]. split; [exact CEIL|]. split; [exact GLO|]. split; [exact LO'|].
  split; [unfold MallocRep.wz; rewrite EA; exact ERR'|]. split; [rewrite (ssp_canary_0 _ _ _ _ HEAP SSP); eapply RHEAP_ssp; exact HEAP'|].
  split; [exact MI'| exact SP16'].
Qed.

Lemma rin_ivs_app : forall X Y a, rin_ivs (X ++ Y) a <-> rin_ivs X a \/ rin_ivs Y a.
Proof. induction X as [|iv X IH]; intros Y a; cbn; [tauto|]. rewrite IH. tauto. Qed.

(* [comment removed for export] *)
Lemma lx_pres_stack : forall s OW LB W m m' SP lo,
  RHEAP s (OW ++ LB) m -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo ->
  munch W m m' -> wmono ctusegs m m' -> Forall (fun iv : Z * Z => lo <= fst iv /\ snd iv <= SP) W ->
  lx_pres LB SP LIBW_AP m m'.
Proof.
  intros s OW LB W m m' SP lo HEAP CEIL GLO MU WM HW.
  eapply lx_pres_of_munch; [exact MU|exact WM|]. intros a Ha [HX Hc]. apply seg_outside. unfold GLOBALS_TOP in GLO.
  eapply Forall_impl; [|exact HW]. intros [x y] [Hx Hy]; cbn [fst snd] in *.
  destruct Hc as [Hc|[(b & Hb & Hr)|Hc]]; [lia| |unfold ralloc_static in Hc; lia].
  destruct b as [[q A] n]. cbn [blk_addr blk_size fst snd] in Hr.
  pose proof (blk_bounds _ _ _ q A n HEAP ltac:(apply in_app_iff; right; exact Hb)). lia.
Qed.

Lemma kept_stack : forall s OW LB W m m' K lo,
  RHEAP s (OW ++ LB) m -> (forall b, In b K -> In b OW) -> alloc_ceiling <= lo ->
  munch W m m' -> Forall (fun iv : Z * Z => lo <= fst iv) W -> kept K m m'.
Proof.
  intros s OW LB W m m' K lo HEAP KOW CEIL MU HW.
  eapply (kept_of_munch s (OW ++ LB) _ m m' K lo); [exact HEAP|intros b Hb; apply in_app_iff; left; apply KOW; exact Hb|exact CEIL|exact MU|].
  eapply Forall_impl; [|exact HW]. intros iv Hx. left. exact Hx.
Qed.

(* [comment removed for export] *)
Lemma ap_state_of_munch_blk : forall st m m' OW E bo s L W lo,
  ap_state st m OW E bo -> RHEAP s L m -> (forall b, In b OW -> In b L) ->
  munch W m m' -> wmono ctusegs m m' -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo ->
  Forall (fun iv => lo <= fst iv \/ iv = (3355012, 3355016)
            \/ (exists p A n, In (p, A, n) L /\ ~ In p (map blk_id OW) /\ A <= fst iv /\ snd iv <= A + n)) W ->
  ap_state st m' OW E bo.
Proof.
  intros st m m' OW E bo s L W lo AS HEAP HL MU WM CEIL GLO HW. eapply ap_state_agree; [exact AS|].
  eapply agree_on_mono; [apply (agree_on_of_munch _ _ _ MU WM)|]. intros a Ha.
  pose proof (lib_addr_where s L m OW a HEAP HL Ha) as C. unfold GLOBALS_TOP in GLO.
  assert (CB : forall p A n, In (p, A, n) L -> ~ In p (map blk_id OW) -> a < A \/ A + n <= a).
  { intros p A n HIn Hni. destruct Ha as [Hs|([[q A'] n'] & Hb & Hr)].
    - pose proof (blk_bounds s L m p A n HEAP HIn) as (B1 & B2 & B3 & B4 & B5). unfold LIBW_HX in Hs. cbn [rin_ivs fst snd] in Hs. lia.
    - cbn [blk_addr blk_size fst snd] in Hr.
      assert (Hpq : p <> q) by (intros ->; apply Hni; change q with (blk_id (q, A', n')); apply in_map; exact Hb).
      pose proof (blk_disjoint s L m p A n q A' n' HEAP HIn (HL _ Hb) Hpq). lia. }
  clear - C CEIL GLO HW CB.
  induction W as [|[x y] W IH]; cbn; [exact I|]. apply Forall_cons_iff in HW. destruct HW as [H1 H2].
  split; [|apply IH; exact H2]. cbn [fst snd] in H1. destruct H1 as [H1|[H1|(p & A & n & HIn & Hni & HA & Hy)]]; [lia| injection H1 as -> ->; lia|].
  pose proof (CB p A n HIn Hni). lia.
Qed.

Lemma lx_pres_munch_gen : forall s OW LB W m m' SP X lo,
  RHEAP s (OW ++ LB) m -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= SP ->
  munch W m m' -> wmono ctusegs m m' ->
  Forall (fun iv => (lo <= fst iv /\ snd iv <= SP) \/ (lo <= fst iv /\ forall a, fst iv <= a < snd iv -> rin_ivs X a)
                    \/ (exists p A n, In (p, A, n) OW /\ A <= fst iv /\ snd iv <= A + n)) W ->
  lx_pres LB SP X m m'.
Proof.
  intros s OW LB W m m' SP X lo HEAP CEIL GLO LOSP MU WM HW.
  eapply lx_pres_of_munch; [exact MU| exact WM|]. intros a Ha [HXa Hc]. unfold GLOBALS_TOP in GLO.
  pose proof (LH_nodup _ _ _ HEAP) as ND. rewrite map_app in ND.
  apply seg_outside. eapply Forall_impl; [| exact HW]. intros [x y] [H|[[Hlo H]|(p & A & n & HIn & HA & Hy)]]; cbn [fst snd] in *.
  - destruct Hc as [Hc|[(b & Hb & Hr)|Hc]]; [lia| | lia].
    destruct b as [[qb A'] n']. cbn [blk_addr blk_size fst snd] in Hr.
    pose proof (blk_bounds _ _ _ qb A' n' HEAP ltac:(apply in_app_iff; right; exact Hb)). lia.
  - destruct (Z.lt_ge_cases a x); [lia|]. destruct (Z.lt_ge_cases a y); [| lia]. exfalso. apply HXa. apply H. lia.
  - pose proof (blk_bounds _ _ _ p A n HEAP ltac:(apply in_app_iff; left; exact HIn)) as (B1 & B2 & B3 & B4 & B5).
    destruct Hc as [Hc|[(b & Hb & Hr)|Hc]]; [lia| | lia].
    destruct b as [[qb A'] n']. cbn [blk_addr blk_size fst snd] in Hr.
    assert (NE : p <> qb).
    { intros ->. exact (NoDup_app_disjoint _ _ qb ND (in_ids _ _ _ _ HIn) (in_ids _ _ _ _ Hb)). }
    pose proof (blk_disjoint _ _ _ p A n qb A' n' HEAP ltac:(apply in_app_iff; left; exact HIn) ltac:(apply in_app_iff; right; exact Hb) NE). lia.
Qed.

(* [comment removed for export] *)
Lemma implM_skip_aret : forall {A} (c : @AM bptr A) (st : ap_st bptr) s Q ms,
  implM ctusegs (interp (ap_embed (abind (aret tt) (fun _ => c) st))) s Q ms -> implM ctusegs (interp (ap_embed (c st))) s Q ms.
Proof. intros A c st s Q ms H. exact H. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition C2I_INT : Z := 0x1144c0.
Definition ASN1_INTEGER_NEW : Z := 0x115194.
(* [comment removed for export] *)
Definition C2I_INT_STACK : Z := 64 + C2I_IBUF_STACK.

(* [comment removed for export] *)
Definition c2i_int_frag (d : list Z) (cont plen : Z) : @AM bptr (option (astr bptr)) :=
  match c2i_ibuf_len d cont plen with
  | IbZero => err_raise RS_zero_content ;;; aret None
  | IbPad => err_raise RS_ill_padding ;;; aret None
  | IbOk r => blk <- amalloc SZ_ASN1_STRING ;; dp <- amalloc r ;; aret (Some (mkStr blk (Some (dp, r))))
  end.

(* [comment removed for export] *)
Definition c2i_int_post (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
    (s : PState) (OW LB : list block) (E : ap_env) (bo : Z * Z) (lo B : Z) (canary : word) (m : mem) (K : list block)
    (D cont plen PV PCONT : Z) (res : ibuf_res)
    (r : option (astr bptr) * ap_st bptr) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (F' : bvmap 5 word) (fc' : bv 32) m' OW' (errv' : word),
    ms' = MS (mkR ra sp gp (wz RATP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom ctusegs)
    /\ frm0 fc' /\ (forall k : reg, bv_unsigned k <> 10 -> reg_get F' k = reg_get F k)
    /\ lx_pres LB (bv_unsigned sp) ([(PV, PV + 8); (PCONT, PCONT + 8)] ++ LIBW_AP) m m'
    /\ ps_so s' = ps_so s /\ ps_fa s' = ps_fa s
    /\ blocks_kept K (snd r) OW' m m'
    /\ match fst r with
       | None => a0 = wz 0 /\ ap_pre s' (snd r) m' OW' LB E bo sp lo B errv' canary 0
                 /\ rw_cells ctusegs m' PV [C8 (wz 0)] /\ rw_cells ctusegs m' PCONT [C8 (wz (D + cont))]
       | Some x => exists blk dp (n A DA ty : Z) (bytes : list byte),
                   x = mkStr blk (Some (dp, n)) /\ n = ibuf_val res /\ 1 <= n <= plen /\ a0 = wz A /\ (ty = 2 \/ ty = 258)
                   /\ blk <> dp /\ ~ In blk (map blk_id (OW' ++ LB)) /\ ~ In dp (map blk_id (OW' ++ LB))
                   /\ rblock_range A ASN1_STRING_SIZE /\ rblock_range DA n
                   /\ RHEAP s' ((dp, DA, n) :: (blk, A, ASN1_STRING_SIZE) :: OW' ++ LB) m' /\ ap_state (snd r) m' OW' E bo /\ ids_ok E (snd r) /\ data_cells m' OW' (snd r)
                   /\ rauxv_ok m' B /\ stk ctusegs m' lo (bv_unsigned sp) /\ rw_cells ctusegs m' 3355012 [C4 errv'] /\ ssp_cells m' canary /\ mem_inv ctusegs m'
                   /\ rw_cells ctusegs m' A (asn1_string_cells n ty DA 0) /\ rw_cells ctusegs m' DA [CB (Z.to_nat n) bytes]
                   /\ rw_cells ctusegs m' PV [C8 (wz A)] /\ rw_cells ctusegs m' PCONT [C8 (wz (D + cont + plen))]
       end.

Definition c2i_int_spec : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (st : ap_st bptr) (OW LB : list block) (E : ap_env) (bo : Z * Z)
         (lo B : Z) (errv canary : word) (K : list block)
         (D : Z) (d : list Z) (cont plen PV PCONT : Z),
    ap_pre s st m OW LB E bo sp lo B errv canary C2I_INT_STACK -> tp = wz RATP -> frm0 fc ->
    (forall b, In b K -> In b OW) -> (forall b, In b K -> ~ In (blk_id b) (es_ids st ++ env_ids E)) ->
    payload_ok m LB D d -> 0 < zlength d -> 0 <= cont -> 0 <= plen < 2^31 -> cont + plen <= zlength d ->
    bv_unsigned sp + 64 <= PV -> bv_unsigned sp + 64 <= PCONT -> PV mod 8 = 0 -> PCONT mod 8 = 0 -> (PV + 8 <= PCONT \/ PCONT + 8 <= PV) -> PV + 8 <= B -> PCONT + 8 <= B ->
    rw_cells ctusegs m PV [C8 (wz 0)] -> rw_cells ctusegs m PCONT [C8 (wz (D + cont))] ->
    a0 = wz PV -> a1 = wz PCONT -> a2 = wz plen ->
    implM ctusegs (interp (ap_embed (c2i_int_frag d cont plen st))) s
          (c2i_int_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F s OW LB E bo lo B canary m K D cont plen PV PCONT (c2i_ibuf_len d cont plen))
          (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (wz C2I_INT) fc None m (seg_rom ctusegs)).

Section Proofs.
  Hypothesis HM : rmalloc_stmt.
  Hypothesis HF : rfree_stmt.

  Section Act.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (m : mem) (s : PState) (st : ap_st bptr) (OW LB : list block) (E : ap_env) (bo : Z * Z) (lo B : Z) (errv canary : word) (K : list block).
  Variables (D : Z) (d : list Z) (cont plen PV PCONT : Z).
  Hypothesis PRE : ap_pre s st m OW LB E bo sp lo B errv canary C2I_INT_STACK.
  Hypothesis TP : tp = wz RATP.
  Hypothesis FRM : frm0 fc.
  Hypothesis KOW : forall b, In b K -> In b OW.
  Hypothesis KIDS : forall b, In b K -> ~ In (blk_id b) (es_ids st ++ env_ids E).
  Hypothesis PAY : payload_ok m LB D d.
  Hypothesis DNE : 0 < zlength d.
  Hypothesis CT0 : 0 <= cont.
  Hypothesis PL0 : 0 <= plen < 2^31.
  Hypothesis CPL : cont + plen <= zlength d.
  Hypothesis PVS : bv_unsigned sp + 64 <= PV.
  Hypothesis PCS : bv_unsigned sp + 64 <= PCONT.
  Hypothesis PV8 : PV mod 8 = 0.
  Hypothesis PC8 : PCONT mod 8 = 0.
  Hypothesis PVC : PV + 8 <= PCONT \/ PCONT + 8 <= PV.
  Hypothesis PVH : PV + 8 <= B.
  Hypothesis PCH : PCONT + 8 <= B.
  Hypothesis HPV : rw_cells ctusegs m PV [C8 (wz 0)].
  Hypothesis HPC : rw_cells ctusegs m PCONT [C8 (wz (D + cont))].

  Local Notation res := (c2i_ibuf_len d cont plen).
  Local Notation W0 := ([(bv_unsigned sp - C2I_INT_STACK, bv_unsigned sp)]%Z) (only parsing).
  Local Notation XC := ([(PV, PV + 8); (PCONT, PCONT + 8)] ++ LIBW_AP) (only parsing).
  Local Notation CPOST := (c2i_int_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F s OW LB E bo lo B canary m K D cont plen PV PCONT res).

  Lemma ctx_facts :
    Forall (fun c => 0 <= c < 256) d /\ 0 < D /\ D + zlength d < 2 ^ 63 /\ zlength d < 2 ^ 30 /\ D + zlength d <= alloc_ceiling
    /\ alloc_ceiling <= lo /\ 3493888 <= lo /\ lo <= bv_unsigned sp - C2I_INT_STACK /\ bv_unsigned sp <= B /\ B < 2 ^ 63 /\ 0 <= bv_unsigned sp < 2 ^ 64
    /\ Z.of_nat (length (to_bytes d)) = zlength d /\ bv_unsigned sp mod 16 = 0
    /\ exists pb PA psz, In (pb, PA, psz) LB /\ PA <= D /\ D + zlength d <= PA + psz /\ (PA + psz <= 0x10000 \/ 0x355000 <= PA).
  Proof using CPL DNE PAY PL0 PRE PV PCONT PVS PCS.
    destruct PRE as (HEAP & AS & IDS & DC & AUX & SPB & B63 & ST & CEIL & GLO & LO & ERR & SSP & MI & SP16).
    destruct PAY as (_ & HF' & D0 & D63 & D30 & HB).
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    destruct HB as [->|(blk & HBLK & BL1 & BL2)]; [exfalso; revert DNE; cbn; unfold zlength; cbn; lia|].
    destruct blk as [[pb PA] psz]. cbn [blk_addr blk_size fst snd] in BL1, BL2.
    pose proof (LH_block_range _ _ _ _ HEAP ltac:(apply in_app_iff; right; exact HBLK)) as (BB0 & BB1 & BB2 & BB3 & BB4). cbn [blk_addr blk_size fst snd] in *.
    unfold GLOBALS_TOP in *.
    repeat (split; [first [assumption|lia]|]). split; [apply zlength_to_bytes|]. split; [exact SP16|].
    exists pb, PA, psz. split; [exact HBLK|]. lia.
  Qed.
  Local Ltac ctx := pose proof ctx_facts as (DF & D0 & D63 & D30 & DCEIL & CEIL & GLO & LO & SPB & B63 & SPR & DLEN & SP16 & pb & PA & psz & HPB & PA1 & PA2 & PA4);
                   unfold C2I_INT_STACK, C2I_IBUF_STACK, ERR_SET_ERROR_STACK in LO.

  Theorem ci_main : forall (t0 t1 t2 t3 a3 a4 a5 a6 a7 : word),
    implM ctusegs (interp (ap_embed (c2i_int_frag d cont plen st))) s CPOST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz PV) (wz PCONT) (wz plen) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz C2I_INT) fc None m (seg_rom ctusegs)).
  Proof using CPL CT0 DNE FRM HF HM HPC HPV KIDS KOW PAY PCH PCS PL0 PRE PVC PVH PVS TP PV8 PC8.
    intros. pose proof PRE as PRE0.
    destruct PRE as (HEAP & AS & IDS & DC & AUX & SPB' & B63' & ST & CEIL' & GLO' & LO' & ERR & SSP & MI & SP16'). ctx.
    pose proof PAY as (HB & _ & _ & _ & _ & HBLK).
    assert (EA : errno_addr (Z_to_bv 64 RATP) = 3355012) by (unfold errno_addr, RATP; rewrite unsigned_lit by lia; reflexivity).
    unfold MallocRep.wz in ERR. rewrite EA in ERR.
    unfold C2I_INT, MallocRep.wz. unfold MallocRep.wz in HPV, HPC.
    pose proof (munch_refl W0 m) as MU. pose proof (wmono_refl ctusegs m) as WM.
    unfold C2I_INT_STACK, C2I_IBUF_STACK, ERR_SET_ERROR_STACK in MU.
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -64)) = bv_unsigned sp + -64) by (apply unsigned_lit; lia).
    unfold implM. iprefix.
    carve_frame 64%nat ST. do 8 step. step.
    step. step. step. step. step. step. rewrite (BnUTac.land7 PCONT PC8).
    name_mem m1.
    (* [comment removed for export] *)
    assert (PRE1 : ap_pre s st m1 OW LB E bo (Z_to_bv 64 (bv_unsigned sp + -64)) lo B errv canary C2I_IBUF_STACK).
    { eapply (ap_pre_seg s st m m1); [exact PRE0| exact MU| exact WM| exact MI| rewrite ESP; exact ST| | rewrite ESP; unfold C2I_IBUF_STACK, ERR_SET_ERROR_STACK; lia| rewrite ESP; lia
        | rewrite ESP; replace (bv_unsigned sp + -64) with (bv_unsigned sp - 64) by lia; rewrite Zminus_mod, SP16; reflexivity| exact ERR].
      constructor; [cbn; lia| constructor]. }
    assert (PAY1 : payload_ok m1 LB D d).
    { destruct PAY as (_ & PF & _ & _ & _ & _). split; [exact HB|]. split; [exact PF|]. split; [lia|]. split; [lia|]. split; [lia|].
      right. exists (pb, PA, psz). split; [exact HPB|]. cbn. lia. }
    assert (LX1 : lx_pres LB (bv_unsigned sp) XC m m1).
    { eapply (lx_pres_munch_gen s OW LB); [exact HEAP| exact CEIL| unfold GLOBALS_TOP; lia| lia| exact MU| exact WM|]. constructor; [left; cbn; lia| constructor]. }
    assert (KP1 : kept K m m1).
    { eapply (kept_stack s OW LB); [exact HEAP| exact KOW| exact CEIL| exact MU|]. constructor; [cbn; lia| constructor]. }
    step. ihere. to_implM.
    unfold c2i_int_frag.
    pose proof (c2i_ibuf_walk HM HF (Z_to_bv 64 (1131784 + 4)) (Z_to_bv 64 (bv_unsigned sp + -64)) gp (Z_to_bv 64 RATP)) as W.
    unfold c2i_ibuf_spec in W. cbv zeta in W.
    (* [comment removed for export] *)
    assert (CALL : forall (X : Type) (REST : unit -> @AM bptr X) Q,
      (forall r1 sA ms1, ibuf_post (Z_to_bv 64 (1131784 + 4)) (Z_to_bv 64 (bv_unsigned sp + -64)) gp sp (Z_to_bv 64 PV) s2 (Z_to_bv 64 PCONT) (Z_to_bv 64 plen) s5 s6 s7 s8 s9 s10 s11
                           F s OW LB E bo lo B canary m1 K res r1 sA ms1 ->
         implM ctusegs (interp (ap_embed (REST (fst r1) (snd r1)))) sA Q ms1) ->
      implM ctusegs (interp (ap_embed (abind (acibuf d cont plen) REST st))) s Q
        (MS (mkR (Z_to_bv 64 (1131784 + 4)) (Z_to_bv 64 (bv_unsigned sp + -64)) gp (Z_to_bv 64 RATP) t0 t1 t2 sp (Z_to_bv 64 PV)
                 (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 (D + cont)) (Z_to_bv 64 plen) a4 a5 a6 a7 s2 (Z_to_bv 64 PCONT) (Z_to_bv 64 plen) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 C2I_IBUF) fc None m1 (seg_rom ctusegs))).
    { intros X REST Q HK. eapply implM_abind; [| exact HK].
      eapply W; [exact PRE1| reflexivity| exact FRM| exact KOW| exact KIDS| exact PAY1| exact DNE| exact CT0| exact PL0| exact CPL| reflexivity| reflexivity| reflexivity| reflexivity]. }
    clear W.
    (* [comment removed for export] *)
    assert (FAIL : forall rz (r1 : unit * ap_st bptr) sA ms1, ibuf_val rz = 0 ->
      ibuf_post (Z_to_bv 64 (1131784 + 4)) (Z_to_bv 64 (bv_unsigned sp + -64)) gp sp (Z_to_bv 64 PV) s2 (Z_to_bv 64 PCONT) (Z_to_bv 64 plen) s5 s6 s7 s8 s9 s10 s11
                F s OW LB E bo lo B canary m1 K rz r1 sA ms1 ->
      implM ctusegs (interp (ap_embed (aret (@None (astr bptr)) (snd r1)))) sA
            (c2i_int_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F s OW LB E bo lo B canary m K D cont plen PV PCONT rz) ms1).
    { intros rz r1 sA ms1 RZ PO1. cbv beta in PO1.
      destruct PO1 as (q0 & q1 & q2 & q11 & q12 & q13 & q14 & q15 & q16 & q17 & q3 & q4 & q5 & q6 & F1 & fc1 & mA & OW1 & errv1
                       & -> & FRM1 & FE1 & PREa & LXa & SOa & FAa & BKa).
      rewrite RZ. unfold MallocRep.wz. replace (ret_pc (Z_to_bv 64 (1131784 + 4))) with (Z_to_bv 64 1131788) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      pose proof PREa as (HEAPa & ASa & IDSa & DCa & AUXa & SPBa & B63a & STa & CEILa & GLOa & LOa & ERRa & SSPa & MIa & SP16a). rewrite ESP in STa.
      unfold MallocRep.wz in ERRa. rewrite EA in ERRa.
      pose proof (agree_of_lx_pres _ _ _ _ _ LXa) as AGa.
      assert (CL : forall a, bv_unsigned sp + -64 <= a -> lx_client LB (bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -64))) LIBW_AP a).
      { intros a Ha. rewrite ESP. split; [unfold LIBW_AP; cbn [rin_ivs fst snd]; lia|left; exact Ha]. }
      apply (rw_cells_agree _ _ _ _ _ AGa) in FR; [|intros a Ha; apply CL; cbn in Ha; lia].
      apply (rw_cells_agree _ _ _ _ _ AGa) in HPV; [|intros a Ha; apply CL; cbn in Ha; lia].
      apply (rw_cells_agree _ _ _ _ _ AGa) in HPC; [|intros a Ha; apply CL; cbn in Ha; lia].
      clear MU WM MI ST HB ERR.
      pose proof (munch_refl (@nil (Z * Z)) mA) as MU. pose proof (wmono_refl ctusegs mA) as WM.
      unfold implM. iprefix. step. if_true. step. step.
      do 7 step. step. release_frame FR STa (bv_unsigned sp). step.
      apply evt_done. cbn [aret ap_embed interp impl]. apply evt_done. unfold epost. cbn [fst snd].
      unfold c2i_int_post. cbn [fst snd].
      eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, F1, fc1, mA, OW1, errv1.
      split; [reflexivity|]. split; [exact FRM1|]. split; [exact FE1|].
      split. { eapply lx_pres_trans; [exact LX1|]. eapply lx_pres_weaken; [exact LXa| rewrite ESP; lia| intros b Hb; exact Hb| intros a Ha; apply rin_ivs_app; right; exact Ha]. }
      split; [exact SOa|]. split; [exact FAa|].
      split. { destruct BKa as (K1 & K2 & K3). split; [exact K1|]. split; [exact K2|]. eapply kept_trans; [exact KP1| exact K3]. }
      split; [reflexivity|].
      split. { eapply (ap_pre_seg sA (snd r1) mA mA) with (W := @nil (Z * Z)); [exact PREa| exact MU| exact WM| exact MIa| exact STa| constructor| lia| lia| exact SP16| exact ERRa]. }
      split; [exact HPV| exact HPC]. }
    destruct (c2i_ibuf_len d cont plen) as [ | |r] eqn:EI.
    - (* [comment removed for export] *)
      replace (err_raise RS_zero_content) with (acibuf d cont plen) by (unfold acibuf; rewrite EI; reflexivity).
      subst tp. apply CALL. intros r1 sA ms1 PO1. eapply FAIL; [reflexivity| exact PO1].
    - (* [comment removed for export] *)
      replace (err_raise RS_ill_padding) with (acibuf d cont plen) by (unfold acibuf; rewrite EI; reflexivity).
      subst tp. apply CALL. intros r1 sA ms1 PO1. eapply FAIL; [reflexivity| exact PO1].
    - (* [comment removed for export] *)
      assert (RF : (r = plen \/ (r = plen - 1 /\ 2 <= plen)) /\ 1 <= r).
      { pose proof EI as H. unfold c2i_ibuf_len in H.
        destruct (Z.eqb_spec plen 0); [discriminate|]. destruct (Z.eqb_spec plen 1) as [E1|N1]; [injection H as ER; lia|].
        set (pad := if znth d cont =? 0 then 1 else _) in H.
        assert (HP : pad = 0 \/ pad = 1) by (subst pad; destruct (znth d cont =? 0); [lia|]; destruct (znth d cont =? 255); [|lia]; destruct (forallb _ _); lia).
        destruct (negb (pad =? 0) && _); [discriminate|]. injection H as ER. lia. }
      destruct RF as [RF R1].
      subst tp. apply implM_skip_aret. replace (aret tt) with (acibuf d cont plen) by (unfold acibuf; rewrite EI; reflexivity).
      apply CALL. intros r1 sA ms1 PO1. cbv beta in PO1. cbn [fst snd].
      destruct PO1 as (q0 & q1 & q2 & q11 & q12 & q13 & q14 & q15 & q16 & q17 & q3 & q4 & q5 & q6 & F1 & fc1 & mA & OW1 & errv1
                       & -> & FRM1 & FE1 & PREa & LXa & SOa & FAa & BKa).
      destruct r1 as [[] st1]. cbn [fst snd] in *.
      cbn [ibuf_val]. unfold MallocRep.wz. replace (ret_pc (Z_to_bv 64 (1131784 + 4))) with (Z_to_bv 64 1131788) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      pose proof PREa as (HEAPa & ASa & IDSa & DCa & AUXa & SPBa & B63a & STa & CEILa & GLOa & LOa & ERRa & SSPa & MIa & SP16a). rewrite ESP in STa.
      unfold MallocRep.wz in ERRa. rewrite EA in ERRa.
      pose proof (agree_of_lx_pres _ _ _ _ _ LXa) as AGa.
      assert (CL : forall a, bv_unsigned sp + -64 <= a -> lx_client LB (bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -64))) LIBW_AP a).
      { intros a Ha. rewrite ESP. split; [unfold LIBW_AP; cbn [rin_ivs fst snd]; lia|left; exact Ha]. }
      apply (rw_cells_agree _ _ _ _ _ AGa) in FR; [|intros a Ha; apply CL; cbn in Ha; lia].
      apply (rw_cells_agree _ _ _ _ _ AGa) in HPV; [|intros a Ha; apply CL; cbn in Ha; lia].
      apply (rw_cells_agree _ _ _ _ _ AGa) in HPC; [|intros a Ha; apply CL; cbn in Ha; lia].
      apply (bytes_at_agree _ _ _ _ _ AGa) in HB.
      2:{ intros a Ha. rewrite ESP. rewrite DLEN in Ha. split; [unfold LIBW_AP; cbn [rin_ivs fst snd]; lia|]. right. left. exists (pb, PA, psz). split; [exact HPB| cbn; lia]. }
      clear MU WM MI ST ERR CALL FAIL.
      assert (KIDSa : forall b, In b K -> ~ In (blk_id b) (es_ids st1 ++ env_ids E)).
      { intros b Hb Hin. apply in_app_iff in Hin. destruct Hin as [Hin|Hin]; [exact (proj1 (proj2 BKa) b Hb Hin)|]. apply (KIDS b Hb). apply in_app_iff. right. exact Hin. }
      pose proof (munch_refl [(bv_unsigned sp - 8480, bv_unsigned sp)]%Z mA) as MU. pose proof (wmono_refl ctusegs mA) as WM.
      unfold implM. iprefix. step. if_cases K0; zc K0; [exfalso; lia|].
      step. step. if_cases K1; zc K1; [exfalso; lia|].
      step. step. if_false.
      (* [comment removed for export] *)
      step. carve_frame 16%nat STa. do 8 step. release_frame FR0 STa (bv_unsigned sp + -64). step.
      name_mem mB.
      assert (PREb : ap_pre sA st1 mB OW1 LB E bo (Z_to_bv 64 (bv_unsigned sp + -64)) lo B errv1 canary (C2I_INT_STACK - 64)).
      { eapply (ap_pre_seg sA st1 mA mB); [exact PREa| exact MU| exact WM| | rewrite ESP| | rewrite ESP; unfold C2I_INT_STACK, C2I_IBUF_STACK, ERR_SET_ERROR_STACK; lia| rewrite ESP; lia
          | rewrite ESP; replace (bv_unsigned sp + -64) with (bv_unsigned sp - 64) by lia; rewrite Zminus_mod, SP16; reflexivity| ]; try assumption.
        constructor; [cbn; lia| constructor]. }
      assert (LXb : lx_pres LB (bv_unsigned sp) XC mA mB).
      { eapply (lx_pres_munch_gen sA OW1 LB); [exact HEAPa| exact CEIL| unfold GLOBALS_TOP; lia| lia| exact MU| exact WM|]. constructor; [left; cbn; lia| constructor]. }
      assert (KPb : kept K mA mB).
      { eapply (kept_stack sA OW1 LB); [exact HEAPa| exact (proj1 BKa)| exact CEIL| exact MU|]. constructor; [cbn; lia| constructor]. }
      clear HEAPa ASa IDSa DCa AUXa STa ERRa SSPa MIa.
      pose proof PREb as (HEAPb & ASb & IDSb & DCb & AUXb & _ & _ & STb & _ & _ & _ & ERRb & SSPb & MIb & _). rewrite ESP in STb.
      unfold MallocRep.wz in ERRb. rewrite EA in ERRb.
      pose proof ASb as (_ & _ & (CSb & RSb & _) & _).
      apply evt_done. cbn [abind apbind amalloc aret ap_embed fst snd]. to_implM.
      eapply (ASN1_STRING_type_new_walk HM) with (B := B) (lo := lo) (errv := errv1) (L := OW1 ++ LB);
        [exact HEAPb | exact AUXb | rewrite ESP; lia | rewrite ESP; exact STb | exact CEIL | unfold GLOBALS_TOP; lia
        | rewrite ESP; unfold ASN1_STRING_TYPE_NEW_STACK, CRYPTO_ZALLOC_STACK, CRYPTO_MALLOC_STACK, RMALLOC_STACK; lia
        | unfold LX_ERRNO, RATP; exact ERRb | exact MIb | reflexivity | exact CSb | reflexivity | lia | reflexivity | ].
      intros pn sN msN PON. unfold calloc_post in PON. rewrite ?ESP in PON.
      destruct PON as (n0 & n1 & n2 & n11 & n12 & n13 & n14 & n15 & n16 & n17 & n3 & n4 & n5 & n6 & mN & A & errvN
                       & -> & MIN & STN & ERRN & AUXN & HPN & FAN & SON & BRN & HEAPN & BLKN).
      replace (ret_pc (Z_to_bv 64 1131820)) with (Z_to_bv 64 1131820) by (symmetry; apply ret_pc_even; [lia| reflexivity]). unfold MallocRep.wz.
      unfold LX_ERRNO, RATP in ERRN. change (3355176 - 164) with 3355012 in ERRN.
      pose proof BRN as (BA0 & BA16 & _ & BAC & BAI). unfold ASN1_STRING_SIZE in *.
      set (pad8 := take 8 _) in FR.
      pose proof (LH_nodup _ _ _ HEAPN) as NDN. cbn [map blk_id fst snd] in NDN.
      assert (NIn : ~ In pn (map blk_id (OW1 ++ LB))) by (apply NoDup_cons_iff in NDN; exact (proj1 NDN)).
      assert (NPn : pb <> pn) by (intros ->; apply NIn; rewrite map_app; apply in_app_iff; right; eapply in_ids; exact HPB).
      pose proof (blk_disjoint _ _ _ pn A 24 pb PA psz HEAPN ltac:(left; reflexivity) ltac:(right; apply in_app_iff; right; exact HPB) ltac:(intros E0; apply NPn; symmetry; exact E0)) as DJn.
      (* [comment removed for export] *)
      pose proof (agree_of_heap_pres _ _ _ _ HPN) as AGN.
      apply (rw_cells_agree _ _ _ _ _ AGN) in FR; [| intros a Ha; left; cbn in Ha; lia].
      apply (rw_cells_agree _ _ _ _ _ AGN) in HPV; [| intros a Ha; left; cbn in Ha; lia].
      apply (rw_cells_agree _ _ _ _ _ AGN) in HPC; [| intros a Ha; left; cbn in Ha; lia].
      apply (bytes_at_agree _ _ _ _ _ AGN) in HB.
      2:{ intros a Ha. right. right. exists (pb, PA, psz). split; [apply in_app_iff; right; exact HPB| cbn; rewrite DLEN in Ha; lia]. }
      assert (ASN : ap_state st1 mN OW1 E bo) by (eapply ap_state_heap_pres_app; [exact ASb| exact HPN]).
      pose proof (ap_state_es _ _ _ _ _ ASb) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & ODb).
      assert (DCN : data_cells mN OW1 st1).
      { eapply data_cells_heap_pres; [exact DCb| exact HPN|]. intros i q k Hd. apply in_app_iff. left. exact (proj1 (optb_ok_nth OW1 _ i q k ODb Hd)). }
      assert (LXN : lx_pres LB (bv_unsigned sp) XC mB mN).
      { eapply lx_pres_weaken; [eapply lx_pres_of_heap_pres; exact HPN| lia| intros b Hb; apply in_app_iff; right; exact Hb| intros a Ha; exact Ha]. }
      assert (KPN : kept K mB mN) by (eapply kept_of_heap_pres; [exact HPN| intros b Hb; apply in_app_iff; left; exact (proj1 BKa b Hb)]).
      clear AGN MU WM HEAPb ASb DCb AUXb STb ERRb SSPb MIb CSb RSb PREb.
      pose proof (munch_refl [(bv_unsigned sp - 8480, bv_unsigned sp); (A, A + 24)]%Z mN) as MU. pose proof (wmono_refl ctusegs mN) as WM.
      unfold asn1_string_cells, MallocRep.wz in BLKN.
      unfold implM. iprefix. step. if_cases K2; zc K2; [exfalso; lia|].
      step. step. step.
      step. step. step. name_mem mC.
      (* [comment removed for export] *)
      assert (HW2 : Forall (fun iv : Z * Z => lo <= fst iv \/ iv = (3355012, 3355016) \/
                 (exists p A' n, In (p, A', n) ((pn, A, 24) :: OW1 ++ LB) /\ ~ In p (map blk_id OW1) /\ A' <= fst iv /\ snd iv <= A' + n))
                 [(bv_unsigned sp - 8480, bv_unsigned sp); (A, A + 24)]%Z).
      { constructor; [left; cbn; lia|]. constructor; [| constructor]. right. right. exists pn, A, 24.
        split; [left; reflexivity|]. split; [intros X; apply NIn; rewrite map_app; apply in_app_iff; left; exact X|]. cbn. lia. }
      assert (HEAPC : RHEAP sN ((pn, A, 24) :: OW1 ++ LB) mC).
      { eapply LH_frame; [exact HEAPN| exact MU| exact WM|]. constructor; [apply W_ok_stack; lia|]. constructor; [| constructor].
        eapply W_ok_block; [left; reflexivity| cbn; lia| cbn; lia]. }
      assert (ASC : ap_state st1 mC OW1 E bo).
      { eapply (ap_state_of_munch_blk st1 mN mC OW1 E bo sN ((pn, A, 24) :: OW1 ++ LB));
          [exact ASN| exact HEAPN| intros b Hb; right; apply in_app_iff; left; exact Hb| exact MU| exact WM| exact CEIL| unfold GLOBALS_TOP; lia| exact HW2]. }
      assert (DCC : data_cells mC OW1 st1).
      { eapply (data_cells_of_munch sN ((pn, A, 24) :: OW1 ++ LB));
          [exact DCN| intros i q k Hd; right; apply in_app_iff; left; exact (proj1 (optb_ok_nth OW1 _ i q k ODb Hd))| exact HEAPN| exact CEIL| exact MU| exact WM|].
        eapply Forall_impl; [| exact HW2]. intros iv [Hx|[Hx|(p & A' & n & H1 & H2 & H3)]]; [left; exact Hx| right; left; exact Hx| right; right].
        exists p, A', n. split; [exact H1|]. split; [| exact H3]. intros i q k Hd E0. apply H2. rewrite <- E0. eapply in_ids. exact (proj1 (optb_ok_nth OW1 _ i q k ODb Hd)). }
      assert (AUXC : rauxv_ok mC B).
      { eapply rauxv_ok_frame; [exact AUXN| exact MU| exact WM|]. constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
      assert (LXC : lx_pres LB (bv_unsigned sp) XC mN mC).
      { eapply (lx_pres_munch_gen sN ((pn, A, 24) :: OW1) LB); [exact HEAPN| exact CEIL| unfold GLOBALS_TOP; lia| lia| exact MU| exact WM|].
        constructor; [left; cbn; lia|]. constructor; [| constructor]. right. right. exists pn, A, 24. split; [left; reflexivity| cbn; lia]. }
      assert (KPC : kept K mN mC).
      { eapply (kept_of_munch sN ((pn, A, 24) :: OW1 ++ LB) _ mN mC K lo); [exact HEAPN| intros b Hb; right; apply in_app_iff; left; exact (proj1 BKa b Hb)| exact CEIL| exact MU|].
        eapply Forall_impl; [| exact HW2]. intros iv [Hx|[Hx|(p & A' & n & H1 & H2 & H3)]]; [left; exact Hx| right; left; exact Hx| right; right].
        exists p, A', n. split; [exact H1|]. split; [| exact H3]. intros X. apply H2.
        apply in_map_iff in X. destruct X as (b & <- & Hb). apply in_map. apply (proj1 BKa). exact Hb. }
      pose proof ASC as (_ & _ & (CSc & RSc & _) & _).
      change [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 2); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] with (asn1_string_cells 0 2 0 0) in BLKN.
      match goal with H : stk ctusegs mC lo _ |- _ => rename H into STc end.
      match goal with H : mem_inv ctusegs mC |- _ => rename H into MIc end.
      match goal with H : rw_cells ctusegs mC 3355012 _ |- _ => rename H into ERRc end.
      (* [comment removed for export] *)
      step. apply evt_done. cbn [abind apbind amalloc aret ap_embed fst snd]. to_implM.
      eapply (ASN1_STRING_set1_data_nosrc_walk HM) with (B := B) (lo := lo) (errv := errvN) (L := (pn, A, 24) :: OW1 ++ LB) (pblk := pn) (n := r);
        [exact HEAPC | exact AUXC | rewrite ESP; lia | rewrite ESP; exact STc | exact CEIL | unfold GLOBALS_TOP; lia
        | rewrite ESP; unfold ASN1_STRING_SET_STACK, CRYPTO_MALLOC_STACK, RMALLOC_STACK; lia
        | unfold LX_ERRNO, RATP; exact ERRc | exact MIc | reflexivity | exact CSc | exact RSc
        | left; reflexivity | exact BLKN | lia | lia | reflexivity | reflexivity | reflexivity | lia | reflexivity | ].
      intros pd sO msO POO. unfold oalloc_post in POO. rewrite ?ESP in POO.
      destruct POO as (o0 & o1 & o2 & o11 & o12 & o13 & o14 & o15 & o16 & o17 & o3 & o4 & o5 & o6 & mO & C & errvO
                       & -> & MIO & STO & ERRO & AUXO & HPO & FAO & SOO & BRO & HEAPO & [bytes DSTO] & CELLO).
      replace (ret_pc (Z_to_bv 64 1131860)) with (Z_to_bv 64 1131860) by (symmetry; apply ret_pc_even; [lia| reflexivity]). unfold MallocRep.wz.
      unfold LX_ERRNO, RATP in ERRO. change (3355176 - 164) with 3355012 in ERRO.
      rewrite (lb_remove_hd pn A 24 (OW1 ++ LB) NDN) in HPO.
      pose proof BRO as (BC0 & BC16 & _ & BCC & BCI).
      pose proof (LH_nodup _ _ _ HEAPO) as NDO. cbn [map blk_id fst snd] in NDO.
      assert (NInD : ~ In pd (pn :: map blk_id (OW1 ++ LB))) by (apply NoDup_cons_iff in NDO; exact (proj1 NDO)).
      assert (NDP : pn <> pd) by (intros ->; apply NInD; left; reflexivity).
      assert (NPd : pb <> pd) by (intros ->; apply NInD; right; rewrite map_app; apply in_app_iff; right; eapply in_ids; exact HPB).
      pose proof (blk_disjoint _ _ _ pd C r pb PA psz HEAPO ltac:(left; reflexivity) ltac:(right; right; apply in_app_iff; right; exact HPB) ltac:(intros E0; apply NPd; symmetry; exact E0)) as DJd.
      pose proof (blk_disjoint _ _ _ pd C r pn A 24 HEAPO ltac:(left; reflexivity) ltac:(right; left; reflexivity) ltac:(intros E0; apply NDP; symmetry; exact E0)) as DJnd.
      (* [comment removed for export] *)
      pose proof (agree_of_heap_pres _ _ _ _ HPO) as AGO.
      apply (rw_cells_agree _ _ _ _ _ AGO) in FR; [| intros a Ha; left; cbn in Ha; lia].
      apply (rw_cells_agree _ _ _ _ _ AGO) in HPV; [| intros a Ha; left; cbn in Ha; lia].
      apply (rw_cells_agree _ _ _ _ _ AGO) in HPC; [| intros a Ha; left; cbn in Ha; lia].
      apply (bytes_at_agree _ _ _ _ _ AGO) in HB.
      2:{ intros a Ha. right. right. exists (pb, PA, psz). split; [apply in_app_iff; right; exact HPB| cbn; rewrite DLEN in Ha; lia]. }
      assert (ASO : ap_state st1 mO OW1 E bo).
      { eapply ap_state_heap_pres; [exact ASC| exact HPO| intros b Hb; apply in_app_iff; left; exact Hb]. }
      assert (DCO : data_cells mO OW1 st1).
      { eapply data_cells_heap_pres; [exact DCC| exact HPO|]. intros i q k Hd. apply in_app_iff. left. exact (proj1 (optb_ok_nth OW1 _ i q k ODb Hd)). }
      assert (LXO : lx_pres LB (bv_unsigned sp) XC mC mO).
      { eapply lx_pres_weaken; [eapply lx_pres_of_heap_pres; exact HPO| lia| intros b Hb; apply in_app_iff; right; exact Hb| intros a Ha; exact Ha]. }
      assert (KPO : kept K mC mO) by (eapply kept_of_heap_pres; [exact HPO| intros b Hb; apply in_app_iff; left; exact (proj1 BKa b Hb)]).
      clear AGO MU WM HEAPC ASC DCC AUXC CSc RSc HEAPN ASN DCN AUXN HW2. try clear STc MIc ERRc STN MIN ERRN BLKN.
      pose proof (munch_refl [(bv_unsigned sp - 8480, bv_unsigned sp); (A, A + 24); (C, C + r); (PV, PV + 8); (PCONT, PCONT + 8)]%Z mO) as MU. pose proof (wmono_refl ctusegs mO) as WM.
      unfold asn1_string_cells, MallocRep.wz in CELLO.
      apply implM_aret.
      step. if_false. step. step. step. step.
      (* [comment removed for export] *)
      lazymatch type of FR with rw_cells _ _ _ (CB 8 ?j :: ?rest) => change (CB 8 j :: rest) with ([CB 8 j] ++ rest) in FR end.
      apply rw_cells_app in FR. destruct FR as [FRA FRB]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FRB.
      assert (FRA' : rw_cells ctusegs mO (bv_unsigned sp + -64) [CB 4 (firstn 4 pad8); CB 4 (skipn 4 pad8)]).
      { pose proof FRA as [[Wf _] _]. cbn in Wf. destruct Wf as [L8 _].
        eapply rw_cells_recast; [exact FRA| cbn; rewrite length_firstn, length_skipn; repeat split; lia| cbn [cells_bytes cbytes app]; rewrite !app_nil_r; symmetry; symmetry; apply firstn_skipn| cbn; lia]. }
      clear FRA. lazymatch type of FRA' with rw_cells _ _ _ [?c1; ?c2] => change [c1; c2] with ([c1] ++ [c2]) in FRA' end.
      apply rw_cells_app in FRA'. destruct FRA' as [FRA FRN]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FRN.
      replace (bv_unsigned sp + -64 + 4) with (bv_unsigned sp + -60) in FRN by lia.
      replace (bv_unsigned sp + -64 + 8) with (bv_unsigned sp + -56) in FRB by lia.
      (* [comment removed for export] *)
      step. eapply evt_cut.
      { eapply (c2i_ibuf_copy_spec) with (m := mO) (lo := lo) (D := D) (d := d) (cont := cont) (plen := plen) (r := r) (C := C) (PNEG := bv_unsigned sp + -60) (junk := bytes) (pj := skipn 4 pad8);
          [exact MIO| rewrite ESP; exact STO| rewrite ESP; lia| exact HB| exact DF| lia| exact CT0| lia| exact CPL| exact EI| exact DSTO| lia| lia| exact FRN| rewrite ESP; lia| clear - SP16; Z.div_mod_to_equations; lia]. }
      (* [comment removed for export] *)
      try phide PA4; try phide RF; try phide SP16; try phide SP16'; try phide BA16; try phide BC16.
      try clear LOa; try clear SPBa; try clear CEILa; try clear GLOa; try clear SP16a; try clear B63a; try clear PREa; try clear PRE1; try clear PAY1; try clear PRE0.
      clear DSTO FRN. post_call_esp ESP mO. rewrite ?ESP in *.
      name_mem mQ.
      match goal with H : rw_cells ctusegs mQ C _ |- _ => rename H into DSTQ end.
      match goal with H : rw_cells ctusegs mQ (bv_unsigned sp + -60) _ |- _ => rename H into FRN end.
      match goal with H : stk ctusegs mQ lo _ |- _ => rename H into STQ end.
      (* [comment removed for export] *)
      step. step. step. step. step. step. step. step. step. step. step.
      pose proof (znth_range d cont DF) as B0R.
      let v := reg_val 12%Z in
      assert (TY : exists ty, (ty = 2 \/ ty = 258) /\ Z_to_bv 64 ty = v)
        by (destruct (land128_cases (znth d cont) B0R) as [(_ & NEG0 & _)|(_ & NEG0 & _)]; rewrite NEG0;
            [exists 2; split; [left; reflexivity|]| exists 258; split; [right; reflexivity|]]; apply bv_eq; vm_compute; reflexivity).
      destruct TY as (ty & TYC & ETY). rewrite <- ETY.
      assert (TYR : 0 <= ty < 2 ^ 32) by (clear - TYC; lia).
      step. step. if_cases K3; zc K3; [exfalso; lia|]. step. step. step.
      do 7 step. step.
      release_frame FRA STQ (bv_unsigned sp + -60). release_frame FRN STQ (bv_unsigned sp + -56). release_frame FRB STQ (bv_unsigned sp). step.
      name_mem mZ. apply evt_done. punhide.
      assert (HWZ : Forall (fun iv : Z * Z => lo <= fst iv \/ iv = (3355012, 3355016) \/
                 (exists p A' n, In (p, A', n) ((pd, C, r) :: (pn, A, 24) :: OW1 ++ LB) /\ ~ In p (map blk_id OW1) /\ A' <= fst iv /\ snd iv <= A' + n))
                 [(bv_unsigned sp - 8480, bv_unsigned sp); (A, A + 24); (C, C + r); (PV, PV + 8); (PCONT, PCONT + 8)]%Z).
      { constructor; [left; cbn; lia|]. constructor.
        { right. right. exists pn, A, 24. split; [right; left; reflexivity|]. split; [intros X; apply NIn; rewrite map_app; apply in_app_iff; left; exact X| cbn; lia]. }
        constructor.
        { right. right. exists pd, C, r. split; [left; reflexivity|]. split; [intros X; apply NInD; right; rewrite map_app; apply in_app_iff; left; exact X| cbn; lia]. }
        constructor; [left; cbn; lia|]. constructor; [left; cbn; lia| constructor]. }
      assert (HEAPZ : RHEAP sO ((pd, C, r) :: (pn, A, 24) :: OW1 ++ LB) mZ).
      { eapply LH_frame; [exact HEAPO| exact MU| exact WM|]. constructor; [apply W_ok_stack; lia|].
        constructor; [eapply W_ok_block; [right; left; reflexivity| cbn; lia| cbn; lia]|].
        constructor; [eapply W_ok_block; [left; reflexivity| cbn; lia| cbn; lia]|].
        constructor; [apply W_ok_stack; lia|]. constructor; [apply W_ok_stack; lia| constructor]. }
      unfold c2i_int_post. cbn [fst snd].
      eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, F1, fc1, mZ, OW1, errvO.
      split; [reflexivity|]. split; [exact FRM1|]. split; [exact FE1|].
      split. { eapply lx_pres_trans; [exact LX1|]. eapply lx_pres_trans; [eapply lx_pres_weaken; [exact LXa| rewrite ?ESP; lia| intros b Hb; exact Hb| intros a Ha; apply rin_ivs_app; right; exact Ha]|].
               eapply lx_pres_trans; [exact LXb|]. eapply lx_pres_trans; [exact LXN|]. eapply lx_pres_trans; [exact LXC|]. eapply lx_pres_trans; [exact LXO|].
               eapply (lx_pres_munch_gen sO ((pd, C, r) :: (pn, A, 24) :: OW1) LB); [exact HEAPO| exact CEIL| unfold GLOBALS_TOP; lia| lia| exact MU| exact WM|].
               constructor; [left; cbn; lia|]. constructor; [right; right; exists pn, A, 24; split; [right; left; reflexivity| cbn; lia]|].
               constructor; [right; right; exists pd, C, r; split; [left; reflexivity| cbn; lia]|].
               constructor; [right; left; split; [cbn; lia| intros a Ha; cbn [rin_ivs fst snd app] in Ha |- *; lia]|].
               constructor; [right; left; split; [cbn; lia| intros a Ha; cbn [rin_ivs fst snd app] in Ha |- *; lia]| constructor]. }
      split; [rewrite SOO, SON; exact SOa|]. split; [rewrite FAO, FAN; exact FAa|].
      split. { destruct BKa as (K1' & K2' & K3'). split; [exact K1'|]. split; [exact K2'|].
               eapply kept_trans; [exact KP1|]. eapply kept_trans; [exact K3'|]. eapply kept_trans; [exact KPb|]. eapply kept_trans; [exact KPN|].
               eapply kept_trans; [exact KPC|]. eapply kept_trans; [exact KPO|].
               eapply (kept_of_munch sO ((pd, C, r) :: (pn, A, 24) :: OW1 ++ LB) _ mO mZ K lo); [exact HEAPO| intros b Hb; right; right; apply in_app_iff; left; exact (K1' b Hb)| exact CEIL| exact MU|].
               eapply Forall_impl; [| exact HWZ]. intros iv [Hx|[Hx|(p & A' & n & H1 & H2 & H3)]]; [left; exact Hx| right; left; exact Hx| right; right].
               exists p, A', n. split; [exact H1|]. split; [| exact H3]. intros X. apply H2.
               apply in_map_iff in X. destruct X as (b & <- & Hb). apply in_map. apply K1'. exact Hb. }
      exists pn, pd, r, A, C, ty, x14.
      split; [reflexivity|]. split; [reflexivity|]. split; [lia|]. split; [reflexivity|]. split; [exact TYC|].
      split; [exact NDP|]. split; [exact NIn|]. split; [intros X; apply NInD; right; exact X|].
      split; [exact BRN|]. split; [exact BRO|]. split; [exact HEAPZ|].
      split. { eapply (ap_state_of_munch_blk st1 mO mZ OW1 E bo sO); [exact ASO| exact HEAPO| intros b Hb; right; right; apply in_app_iff; left; exact Hb| exact MU| exact WM| exact CEIL| unfold GLOBALS_TOP; lia| exact HWZ]. }
      split; [exact IDSb|].
      split. { eapply (data_cells_of_munch sO ((pd, C, r) :: (pn, A, 24) :: OW1 ++ LB));
                 [exact DCO| intros i q k Hd; right; right; apply in_app_iff; left; exact (proj1 (optb_ok_nth OW1 _ i q k ODb Hd))| exact HEAPO| exact CEIL| exact MU| exact WM|].
               eapply Forall_impl; [| exact HWZ]. intros iv [Hx|[Hx|(p & A' & n & H1 & H2 & H3)]]; [left; exact Hx| right; left; exact Hx| right; right].
               exists p, A', n. split; [exact H1|]. split; [| exact H3]. intros i q k Hd E0. apply H2. rewrite <- E0. eapply in_ids. exact (proj1 (optb_ok_nth OW1 _ i q k ODb Hd)). }
      split. { eapply rauxv_ok_frame; [exact AUXO| exact MU| exact WM|].
               repeat (constructor; [cbn; unfold RAUXV_CELL; first [solve [clear - LO SPR GLO CEIL BAC BCC BAI BCI BA0 BC0 PVS PCS; lia] | lia]|]). constructor. }
      split; [exact STQ|]. split; [exact ERRO|]. split; [rewrite (ssp_canary_0 _ _ _ _ HEAP SSP); eapply RHEAP_ssp; exact HEAPZ|]. split; [exact MI|].
      split; [| split; [exact DSTQ| split; [exact HPV| unfold MallocRep.wz; replace (D + cont + plen) with (plen + (D + cont)) by lia; exact HPC]]].
      match goal with H : rw_cells ctusegs mZ A [?c1; C4 ?w; ?c3; ?c4] |- _ => replace w with (Z_to_bv 64 ty) in H by exact ETY; exact H end.
  Qed.

  End Act.

  (* [comment removed for export] *)
  Theorem c2i_int_walk : c2i_int_spec.
  Proof using HF HM.
    unfold c2i_int_spec. intros until PCONT. intros PRE TP FRM KOW KIDS PAY DNE CT0 PL0 CPL PVS PCS PV8 PC8 PVC PVH PCH HPV HPC -> -> ->.
    eapply (ci_main ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 t6 F fc m s st OW LB E bo lo B errv canary K D d cont plen PV PCONT);
      assumption.
  Qed.
End Proofs.
End WithCeiling0.
