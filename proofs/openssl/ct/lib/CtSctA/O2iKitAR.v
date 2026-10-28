(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim STree Malloc Monad Stdio Prog LibProg ProgG CtSizes CtWire CtModel ApBase ApState ApErr ApParse ApBridge.
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame Cells Step Mem RzCPS. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface RT_client_kit D_defs D_cs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import R_unwind_chain.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtKitA Require Import RT_iface2 LibKitA ARun BnHeapA BnRepDefs BnRepA ImplA BnIfaceA UnwindA W_cryptoA UnwindX.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepP Require Import ApCells ApErrKit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepP Require ApIface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import ApRepDefs ApRep ApIface ApFrame ApErrKitA2 W_akit W_get_objectA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtFrameA Require Import AFrameKit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctP Require Import SctDefs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctP Require SctRep W_sct_list_free.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctA Require Import SctRepA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma land_ones64_neg : forall x, - 2 ^ 64 <= x < 0 -> Z.land x 18446744073709551615 = x + 2 ^ 64.
Proof.
  intros x Hx. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia.
  rewrite <- (Z.mod_add x 1 (2 ^ 64)) by lia. rewrite Z.mod_small by lia. lia.
Qed.
Lemma land_ones64_small : forall x, 0 <= x < 2 ^ 64 -> Z.land x 18446744073709551615 = x.
Proof. intros x Hx. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.

Lemma rin_ivs_app_iff : forall X Y a, rin_ivs (X ++ Y) a <-> rin_ivs X a \/ rin_ivs Y a.
Proof. intros X Y a. induction X as [|iv X IH]; cbn [rin_ivs app]; [tauto|]. rewrite IH. tauto. Qed.
Lemma rin_ivs_In : forall X a, rin_ivs X a <-> exists iv, In iv X /\ fst iv <= a < snd iv.
Proof.
  intros X a. induction X as [|iv X IH]; cbn [rin_ivs].
  - split; [intros []| intros (iv & [] & _)].
  - rewrite IH. split.
    + intros [H|(iv' & H1 & H2)]; [exists iv; split; [left; reflexivity| exact H]| exists iv'; split; [right; exact H1| exact H2]].
    + intros (iv' & [<-|H1] & H2); [left; exact H2| right; exists iv'; split; [exact H1| exact H2]].
Qed.
Lemma libw_rangeA : forall a, rin_ivs LIBW_A a -> 0x5aebe0 <= a < 0xbcab98.
Proof. intros a Ha. unfold LIBW_A in Ha. cbn [rin_ivs fst snd] in Ha. lia. Qed.
Lemma client_static_below : forall a, client_static a -> a < 12365824.
Proof.
  intros a [(l & h & Hin & Hlh) _]. unfold CLIENT_STATIC in Hin. cbn [In] in Hin.
  destruct Hin as [E0|[E0|[E0|[]]]]; injection E0 as <- <-; lia.
Qed.

Lemma nodup_app_r : forall {A} (l1 l2 : list A), List.NoDup (l1 ++ l2) -> List.NoDup l2.
Proof. intros A l1 l2 H. induction l1 as [|x l1 IH]; [exact H|]. cbn in H. apply NoDup_cons_iff in H as [_ H]. exact (IH H). Qed.
Lemma Forall_perm : forall {A} (P : A -> Prop) (l l' : list A), Permutation l l' -> Forall P l -> Forall P l'.
Proof. intros A P l l' HP HF. apply Forall_forall. intros x Hx. apply (proj1 (Forall_forall _ _) HF). eapply Permutation_in; [symmetry; exact HP| exact Hx]. Qed.

Section WithRT.
Context {AR : ARun} {UK : UnwindKit}.
Local Notation RT := (@ar_RT AR).
Local Notation FR := (@ar_FR AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).

(* [comment removed for export] *)
Lemma AH_lb_perm : forall Σ OW LB LB' m, AHEAP Σ OW LB m -> Permutation LB LB' -> AHEAP Σ OW LB' m.
Proof.
  intros Σ OW LB LB' m (HA & HS & HFr & SPL & ND & HF1 & HF2) P.
  split; [exact HA|]. split; [exact HS|]. split; [exact HFr|]. split.
  - destruct SPL as (FW & PB & LBr & P1 & P2 & F & AP). split; [exact FW|]. exists PB, LBr.
    split; [eapply Permutation_trans; [symmetry; exact P| exact P1]|]. split; [exact P2|]. split; [exact F| exact AP].
  - split; [eapply nodup_ids_perm; [apply Permutation_app_head; exact P| exact ND]|].
    split; [exact HF1|]. eapply Forall_perm; [exact P| exact HF2].
Qed.

(* [comment removed for export] *)
Lemma AH_blk : forall Σ OW LB m b, AHEAP Σ OW LB m -> In b (OW ++ LB) ->
  0 < blk_addr b /\ 0 <= blk_size b /\ blk_addr b + blk_size b <= ACEIL /\ (blk_addr b + blk_size b <= 65536 \/ 12365824 <= blk_addr b).
Proof. intros Σ OW LB m b H Hb. pose proof (AH_range_gen _ _ _ _ b H Hb) as (R1 & _ & R3 & R4 & R5). repeat split; assumption. Qed.

(* [comment removed for export] *)
Definition kit_hyps (sp : word) (LB : list block) (lo : Z) (c : list Z) (D : Z) (XP : list (Z * Z)) (spa STK : Z) : Prop :=
  Forall (fun b => 0 <= b < 256) c /\ ACEIL <= lo /\ 0 <= lo /\ lo <= spa - STK /\ 0 <= STK /\ spa <= bv_unsigned sp
  /\ bv_unsigned sp + 16 <= USTACK_TOP /\ bv_unsigned sp mod 16 = 0 /\ spa mod 16 = 0
  /\ Forall (fun iv : Z * Z => exists b, In b LB /\ blk_addr b <= fst iv /\ snd iv <= blk_addr b + blk_size b) XP
  /\ Forall (fun iv : Z * Z => c = [] \/ snd iv <= D \/ D + zlength c <= fst iv) XP
  /\ (c = [] \/ exists pb PA psz, In (pb, PA, psz) LB /\ PA <= D /\ D + zlength c <= PA + psz)
  /\ 0 <= D.

Section Act.
  Variables (sp : word) (m : mem) (Σ : rts RT) (LB : list block) (E : ap_env) (lo : Z) (K : list block).
  Variables (c : list Z) (D : Z) (XP : list (Z * Z)) (spa STK CST FRM : Z).   (* [comment removed for export] *)
  Hypothesis KH : kit_hyps sp LB lo c D XP spa STK.
  Local Ltac kh := destruct KH as (DF & CEIL & LO0 & LO & STK0 & OFS0 & TOP & SP16 & OFS16 & XPok & XPD & PBX & D0).  (* [comment removed for export] *)

  Local Notation X0 := (XP ++ LIBW_A) (only parsing).

  Lemma SPR : 0 <= bv_unsigned sp < 2 ^ 64.
  Proof. kh. pose proof (bv_unsigned_in_range 64 sp) as H. unfold bv_modulus in H. cbn in H. exact H. Qed.
  Lemma DLEN : Z.of_nat (length (to_bytes c)) = zlength c.
  Proof. kh. clear. unfold to_bytes, zlength; rewrite length_map; reflexivity. Qed.
  Lemma ESP : bv_unsigned (Z_to_bv 64 spa) = spa.
  Proof. pose proof SPR. kh. clear - H LO0 LO STK0 OFS0. apply unsigned_lit; lia. Qed.
  Lemma SPO : spa mod 16 = 0.
  Proof. kh. exact OFS16. Qed.

  Definition oinv (ΣX : rts RT) (stX : ap_st bptr) (mX : mem) (OWX : list block) (boX : Z * Z) (NEW : list block) (CX : Z) : Prop :=
    ap_preA ΣX stX mX OWX (NEW ++ LB) E boX (Z_to_bv 64 spa) lo STK CX FRM
    /\ ax_pres LB (bv_unsigned sp) X0 m mX
    /\ (forall b, In b K -> In b OWX) /\ (forall b, In b K -> ~ In (blk_id b) (es_ids stX ++ env_ids E)) /\ kept K m mX
    /\ bytes_at ctasegs mX D (to_bytes c)
    /\ rt_credit RT Σ - CST + CX <= rt_credit RT ΣX
    /\ Forall lbokA NEW.
    (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma oinv_entry : forall st OW bo,
    ap_preA Σ st m OW LB E bo (Z_to_bv 64 spa) lo STK CST FRM ->
    (forall b, In b K -> In b OW) -> (forall b, In b K -> ~ In (blk_id b) (es_ids st ++ env_ids E)) ->
    bytes_at ctasegs m D (to_bytes c) ->
    oinv Σ st m OW bo [] CST.
  Proof.
    kh. intros st OW bo PRE KOW KIDS HB.
    split; [| split; [apply ax_pres_refl| split; [exact KOW| split; [exact KIDS| split; [apply kept_refl| split; [exact HB| split; [clear; lia| constructor]]]]]]].
    cbn [app]. exact PRE.
  Qed.

  (* [comment removed for export] *)
  Lemma oinv_facts : forall ΣX stX mX OWX boX NEW CX,
    oinv ΣX stX mX OWX boX NEW CX ->
    AHEAP ΣX OWX (NEW ++ LB) mX /\ List.NoDup (map blk_id (OWX ++ NEW ++ LB))
    /\ (forall b, In b (OWX ++ NEW ++ LB) -> 0 < blk_addr b /\ 0 <= blk_size b /\ blk_addr b + blk_size b <= ACEIL /\ (blk_addr b + blk_size b <= 65536 \/ 12365824 <= blk_addr b))
    /\ (forall b, In b NEW -> ~ In (blk_id b) (map blk_id (OWX ++ LB)))
    /\ (forall b b', In b NEW -> In b' LB -> blk_addr b + blk_size b <= blk_addr b' \/ blk_addr b' + blk_size b' <= blk_addr b)
    /\ (forall b b', In b NEW -> In b' OWX -> blk_addr b + blk_size b <= blk_addr b' \/ blk_addr b' + blk_size b' <= blk_addr b).
  Proof.
    kh. intros until CX. intros (PREX & _). destruct PREX as (HEAP & _).
    pose proof (AH_nodup _ _ _ _ HEAP) as ND.
    assert (FRSH : forall b, In b NEW -> ~ In (blk_id b) (map blk_id (OWX ++ LB))).
    { intros b Hb Hin. rewrite !map_app in ND. rewrite map_app in Hin. apply in_app_iff in Hin.
      pose proof (in_map blk_id _ _ Hb) as IQ.
      destruct Hin as [Hin|Hin].
      - exact (NoDup_app_disjoint _ _ _ ND Hin ltac:(apply in_app_iff; left; exact IQ)).
      - pose proof (nodup_app_r _ _ ND) as N23. exact (NoDup_app_disjoint _ _ _ N23 IQ Hin). }
    split; [exact HEAP|]. split; [exact ND|]. split; [intros b Hb; exact (AH_blk _ _ _ _ b HEAP Hb)|]. split; [exact FRSH|]. split.
    - intros b b' Hb Hb'. apply (AH_disjoint_gen _ _ _ _ b b' HEAP); [apply in_app_iff; right; apply in_app_iff; left; exact Hb| apply in_app_iff; right; apply in_app_iff; right; exact Hb'|].
      intros E0. apply (FRSH b Hb). rewrite map_app. apply in_app_iff. right. rewrite E0. apply in_map. exact Hb'.
    - intros b b' Hb Hb'. apply (AH_disjoint_gen _ _ _ _ b b' HEAP); [apply in_app_iff; right; apply in_app_iff; left; exact Hb| apply in_app_iff; left; exact Hb'|].
      intros E0. apply (FRSH b Hb). rewrite map_app. apply in_app_iff. left. rewrite E0. apply in_map. exact Hb'.
  Qed.

  (* [comment removed for export] *)
  Definition own_iv (NEW : list block) (iv : Z * Z) : Prop :=
    (lo <= fst iv /\ snd iv <= bv_unsigned sp) \/ (exists xiv, In xiv XP /\ fst xiv <= fst iv /\ snd iv <= snd xiv)
    \/ (exists b, In b NEW /\ blk_addr b <= fst iv /\ snd iv <= blk_addr b + blk_size b).

  Lemma lib_out_own : forall ΣX (OWX NEW : list block) mX W a,
    AHEAP ΣX OWX (NEW ++ LB) mX -> Forall (own_iv NEW) W -> lib_addr OWX a -> outside W a.
  Proof.
    kh. intros ΣX OWX NEW mX W a HEAP HW HL. pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & _ & _). unfold SEGTOP_A in C1.
    pose proof (AH_nodup _ _ _ _ HEAP) as ND.
    assert (XPF : forall iv, In iv XP -> exists b, In b LB /\ blk_addr b <= fst iv /\ snd iv <= blk_addr b + blk_size b)
      by (intros iv Hiv; exact (proj1 (Forall_forall _ _) XPok iv Hiv)).
    induction W as [|[x y] W IH]; cbn [outside]; [exact I|]. apply Forall_cons_iff in HW as [H1 H2]. split; [| exact (IH H2)].
    destruct HL as [HS|(bo & Hbo & Hr)].
    - pose proof (libw_rangeA a (LIBW_S_A a HS)) as RA. pose proof (ar_LIBW_cs a (LIBW_S_A a HS)) as CS.
      destruct H1 as [[L1 L2]|[(xiv & HX & X1 & X2)|(b & Hb & L1 & L2)]]; cbn [fst snd] in *.
      + clear - RA C1 CEIL L1 L2. lia.
      + destruct (XPF _ HX) as (b & Hb & B1 & B2). intros Ha.
        exact (blk_not_static ΣX OWX (NEW ++ LB) mX b a HEAP ltac:(apply in_app_iff; right; apply in_app_iff; right; exact Hb) ltac:(clear - Ha B1 B2 X1 X2; lia) CS).
      + intros Ha. exact (blk_not_static ΣX OWX (NEW ++ LB) mX b a HEAP ltac:(apply in_app_iff; right; apply in_app_iff; left; exact Hb) ltac:(clear - Ha L1 L2; lia) CS).
    - assert (Hbo' : In bo (OWX ++ NEW ++ LB)) by (apply in_app_iff; left; exact Hbo).
      pose proof (AH_blk _ _ _ _ bo HEAP Hbo') as (_ & _ & R3 & _).
      destruct H1 as [[L1 L2]|[(xiv & HX & X1 & X2)|(b & Hb & L1 & L2)]]; cbn [fst snd] in *.
      + clear - Hr R3 CEIL L1 L2. lia.
      + destruct (XPF _ HX) as (b & Hb & B1 & B2).
        pose proof (AH_disjoint_gen _ _ _ _ bo b HEAP Hbo' ltac:(apply in_app_iff; right; apply in_app_iff; right; exact Hb)
                      ltac:(apply not_eq_sym; destruct bo as [[q A] n]; exact (ids_disj OWX (NEW ++ LB) q A n ND Hbo b ltac:(apply in_app_iff; right; exact Hb)))) as DJ.
        clear - Hr DJ B1 B2 X1 X2. lia.
      + pose proof (AH_disjoint_gen _ _ _ _ bo b HEAP Hbo' ltac:(apply in_app_iff; right; apply in_app_iff; left; exact Hb)
                      ltac:(apply not_eq_sym; destruct bo as [[q A] n]; exact (ids_disj OWX (NEW ++ LB) q A n ND Hbo b ltac:(apply in_app_iff; left; exact Hb)))) as DJ.
        clear - Hr DJ L1 L2. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma ax_out_own : forall ΣX (OWX NEW : list block) mX W a,
    AHEAP ΣX OWX (NEW ++ LB) mX -> Forall (own_iv NEW) W -> (forall b, In b NEW -> ~ In (blk_id b) (map blk_id (OWX ++ LB))) ->
    ax_client LB (bv_unsigned sp) X0 a -> outside W a.
  Proof.
    kh. intros ΣX OWX NEW mX W a HEAP HW FRSH [HX Hc]. pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & _ & _). unfold SEGTOP_A in C1.
    assert (NXP : forall iv, In iv XP -> ~ (fst iv <= a < snd iv)).
    { intros iv Hiv Ha. apply HX. apply rin_ivs_app_iff. left. apply rin_ivs_In. exists iv. split; [exact Hiv| exact Ha]. }
    induction W as [|[x y] W IH]; cbn [outside]; [exact I|]. apply Forall_cons_iff in HW as [H1 H2]. split; [| exact (IH H2)].
    destruct H1 as [[L1 L2]|[(xiv & HXi & X1 & X2)|(b & Hb & L1 & L2)]]; cbn [fst snd] in *.
    - destruct Hc as [Hc|[Hc|(b & Hb & Hr)]]; [clear - Hc L1 L2; lia| pose proof (client_static_below a Hc); clear - H C1 CEIL L1 L2; lia|].
      pose proof (AH_blk _ _ _ _ b HEAP ltac:(apply in_app_iff; right; apply in_app_iff; right; exact Hb)) as (_ & _ & R3 & _). clear - Hr R3 CEIL L1 L2. lia.
    - intros Ha. apply (NXP _ HXi). clear - Ha X1 X2. lia.
    - assert (Hb' : In b (OWX ++ NEW ++ LB)) by (apply in_app_iff; right; apply in_app_iff; left; exact Hb).
      pose proof (AH_blk _ _ _ _ b HEAP Hb') as (_ & _ & R3 & _).
      destruct Hc as [Hc|[Hc|(b' & Hb2 & Hr)]]; [clear - Hc R3 CEIL L1 L2 LO STK0 OFS0; lia
        | intros Ha; exact (blk_not_static ΣX OWX (NEW ++ LB) mX b a HEAP Hb' ltac:(clear - Ha L1 L2; lia) Hc)|].
      pose proof (AH_disjoint_gen _ _ _ _ b b' HEAP Hb' ltac:(apply in_app_iff; right; apply in_app_iff; right; exact Hb2)
                    ltac:(intros E0; apply (FRSH b Hb); rewrite map_app; apply in_app_iff; right; rewrite E0; apply in_map; exact Hb2)) as DJ.
      clear - Hr DJ L1 L2. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma oinv_munch : forall ΣX stX mX OWX boX NEW CX mY W,
    oinv ΣX stX mX OWX boX NEW CX ->
    munch W mX mY -> wmono ctasegs mX mY -> mem_inv ctasegs mY -> stk ctasegs mY lo spa ->
    Forall (own_iv NEW) W ->
    oinv ΣX stX mY OWX boX NEW CX.
  Proof.
    kh. intros until W. intros OI MU WM MI ST HW. pose proof SPR as SPR. pose proof DLEN as DLEN.
    pose proof (oinv_facts _ _ _ _ _ _ _ OI) as (HEAP3 & ND3 & BND & FRSH & DJL & DJO).
    destruct OI as (PREX & AX & KO & KI & KP & HB & CR & LBOK).
    destruct PREX as (HEAP & AS & IDS & DC & ST0 & CEIL' & LOSP & TOP' & AL16 & MI0 & CRED & FRM').
    pose proof ESP as ESP. rewrite ESP in *.
    pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & _ & C3). unfold SEGTOP_A in C1.
    assert (XPF : forall iv, In iv XP -> exists b, In b LB /\ blk_addr b <= fst iv /\ snd iv <= blk_addr b + blk_size b)
      by (intros iv Hiv; exact (proj1 (Forall_forall _ _) XPok iv Hiv)).
    assert (AGL : agree_on (lib_addr OWX) mX mY).
    { eapply agree_on_mono; [exact (agree_on_of_munch_nw _ _ _ MU)|]. intros a HL. exact (lib_out_own ΣX OWX NEW mX W a HEAP HW HL). }
    assert (HEAPY : AHEAP ΣX OWX (NEW ++ LB) mY).
    { eapply AH_frame; [exact HEAP| exact MU| exact WM|]. eapply Forall_impl; [| exact HW].
      intros [x y] [[L1 L2]|[HX|(b & Hb & L1 & L2)]]; cbn [fst snd] in *.
      - left. cbn [fst snd]. clear - L1 L2 CEIL TOP C3. unfold USTACK_TOP, STACK_WIN in *. lia.
      - destruct HX as (xiv & HX & X1 & X2). destruct (XPF _ HX) as (b & Hb & B1 & B2). right; right. exists b.
        split; [apply in_app_iff; right; apply in_app_iff; right; exact Hb| cbn [fst snd]; clear - B1 B2 X1 X2; lia].
      - right; right. exists b. split; [apply in_app_iff; right; apply in_app_iff; left; exact Hb| cbn [fst snd]; exact (conj L1 L2)]. }
    pose proof (ap_state_esA _ _ _ _ _ AS) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & OD).
    split; [| split; [| split; [exact KO| split; [exact KI| split; [| split; [| split; [exact CR| exact LBOK]]]]]]].
    - unfold ap_preA. rewrite ESP. split; [exact HEAPY|]. split; [exact (ap_state_agree _ _ _ _ _ _ AS AGL)|]. split; [exact IDS|].
      split; [exact (data_cells_agree _ _ _ _ DC AGL OD)|]. split; [exact ST|]. split; [exact CEIL|]. split; [exact LOSP|]. split; [exact TOP'|].
      split; [exact AL16|]. split; [exact MI|]. split; [exact CRED| exact FRM'].
    - eapply ax_pres_trans; [exact AX|]. unfold ax_pres. eapply agree_on_mono; [exact (agree_on_of_munch_nw _ _ _ MU)|].
      intros a Ha. exact (ax_out_own ΣX OWX NEW mX W a HEAP HW FRSH Ha).
    - eapply kept_trans; [exact KP|]. intros a Ha Hin. apply MU. unfold wa. rewrite unsigned_lit by exact Ha.
      apply (lib_out_own ΣX OWX NEW mX W a HEAP HW). right. eapply in_block_mono; [exact KO| exact Hin].
    - destruct c as [|c0 c'].
      { destruct HB as (HB0 & HB1 & _). split; [exact HB0|]. split; [exact HB1|]. intros i Hi. cbn in Hi. clear - Hi. lia. }
      destruct PBX as [E0|(pb & PA & psz & HPB & PB1 & PB2)]; [discriminate E0|].
      eapply bytes_at_transport; [exact HB| exact MU|]. rewrite DLEN.
      assert (HPB' : In (pb, PA, psz) (OWX ++ NEW ++ LB)) by (apply in_app_iff; right; apply in_app_iff; right; exact HPB).
      pose proof (BND _ HPB') as (_ & _ & P3 & _). cbn [blk_addr blk_size fst snd] in P3.
      clear - HW XPD DJL HPB HPB' PB1 PB2 P3 CEIL. induction W as [|[x y] W IH]; cbn [disjoint_from]; [exact I|].
      apply Forall_cons_iff in HW as [H1 H2]. split; [| exact (IH H2)].
      destruct H1 as [[L1 L2]|[HXi|(b & Hb & L1 & L2)]]; cbn [fst snd] in *.
      + clear - L1 PB2 P3 CEIL. lia.
      + destruct HXi as (xiv & HXi & Y1 & Y2). pose proof (proj1 (Forall_forall _ _) XPD _ HXi) as [E0|X1]; [discriminate E0|]. clear - X1 Y1 Y2. lia.
      + pose proof (DJL b (pb, PA, psz) Hb HPB) as DJ. cbn [blk_addr blk_size fst snd] in DJ. clear - DJ PB1 PB2 L1 L2. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma xp_not_lib : forall ΣX (OWX NEW : list block) mX a,
    AHEAP ΣX OWX (NEW ++ LB) mX -> lib_addr OWX a -> ~ rin_ivs XP a.
  Proof.
    kh. intros ΣX OWX NEW mX a HEAP HL HX. apply rin_ivs_In in HX. destruct HX as (iv & Hiv & Hr).
    pose proof (lib_out_own ΣX OWX NEW mX [iv] a HEAP ltac:(constructor; [right; left; exists iv; split; [exact Hiv| split; apply Z.le_refl]| constructor]) HL) as O.
    destruct iv as [x y]. cbn [outside fst snd] in O, Hr. exact (proj1 O Hr).
  Qed.
  Lemma xp_not_pay : forall a, c <> [] -> D <= a < D + zlength c -> ~ rin_ivs XP a.
  Proof.
    kh. intros a NE Ha HX. apply rin_ivs_In in HX. destruct HX as (iv & Hiv & Hr).
    pose proof (proj1 (Forall_forall _ _) XPD _ Hiv) as [E0|X1]; [exact (NE E0)|]. clear - Ha Hr X1. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma oinv_heap : forall ΣX stX mX OWX boX NEW CX ΣY mY (L1 NEW' : list block) cst,
    oinv ΣX stX mX OWX boX NEW CX ->
    agree_on (fun a => aclient_addr L1 spa a /\ ~ rin_ivs XP a) mX mY -> (forall b, In b OWX \/ In b LB -> In b L1) ->
    AHEAP ΣY OWX (NEW' ++ LB) mY -> Forall lbokA NEW' ->
    mem_inv ctasegs mY -> stk ctasegs mY lo spa ->
    rt_credit RT ΣX - cst <= rt_credit RT ΣY -> 0 <= cst <= CX ->
    oinv ΣY stX mY OWX boX NEW' (CX - cst).
  Proof.
    kh. intros until cst. intros OI AG HL1 HEAPY LBOK' MI ST CRY HC. pose proof SPR as SPR. pose proof DLEN as DLEN.
    pose proof (oinv_facts _ _ _ _ _ _ _ OI) as (HEAP3 & ND3 & BND & FRSH & DJL & DJO).
    destruct OI as (PREX & AX & KO & KI & KP & HB & CR & LBOK).
    destruct PREX as (HEAP & AS & IDS & DC & ST0 & CEIL' & LOSP & TOP' & AL16 & MI0 & CRED & FRM').
    pose proof ESP as ESP. rewrite ESP in *.
    assert (AGL : agree_on (lib_addr OWX) mX mY).
    { eapply agree_on_mono; [exact AG|]. intros a HL. split; [| exact (xp_not_lib ΣX OWX NEW mX a HEAP HL)]. destruct HL as [HS|(b & Hb & Hr)].
      - right; left. exact (ar_LIBW_cs a (LIBW_S_A a HS)).
      - right; right. exists b. split; [apply HL1; left; exact Hb| exact Hr]. }
    pose proof (ap_state_esA _ _ _ _ _ AS) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & OD).
    split; [| split; [| split; [exact KO| split; [exact KI| split; [| split; [| split; [clear - CR CRY HC; lia| exact LBOK']]]]]]].
    - unfold ap_preA. rewrite ESP. split; [exact HEAPY|]. split; [exact (ap_state_agree _ _ _ _ _ _ AS AGL)|]. split; [exact IDS|].
      split; [exact (data_cells_agree _ _ _ _ DC AGL OD)|]. split; [exact ST|]. split; [exact CEIL|]. split; [exact LOSP|]. split; [exact TOP'|].
      split; [exact AL16|]. split; [exact MI|]. split; [clear - CRED CRY HC; lia|].
      exact FRM'.
    - eapply ax_pres_trans; [exact AX|]. unfold ax_pres. eapply agree_on_mono; [exact AG|].
      intros a [HX Hc]. split; [| intros HIN; apply HX; apply rin_ivs_app_iff; left; exact HIN].
      destruct Hc as [Ha|[Ha|(b & Hb & Hr)]]; [left; clear - Ha OFS0; lia| right; left; exact Ha| right; right; exists b; split; [apply HL1; right; exact Hb| exact Hr]].
    - eapply kept_trans; [exact KP|]. intros a Ha Hin. apply (AG a Ha).
      assert (HL : lib_addr OWX a) by (right; eapply in_block_mono; [exact KO| exact Hin]).
      split; [| exact (xp_not_lib ΣX OWX NEW mX a HEAP HL)]. right; right. destruct Hin as (b & Hb & Hr). exists b. split; [apply HL1; left; apply KO; exact Hb| exact Hr].
    - pose proof xp_not_pay as XNP. destruct c as [|c0 c'].
      { destruct HB as (HB0 & HB1 & _). split; [exact HB0|]. split; [exact HB1|]. intros i Hi. cbn in Hi. clear - Hi. lia. }
      destruct PBX as [E0|(pb & PA & psz & HPB & PB1 & PB2)]; [discriminate E0|].
      eapply bytes_at_agree; [exact AG| exact HB|]. intros a Ha. rewrite DLEN in Ha. split; [| apply XNP; [discriminate| exact Ha]].
      right; right. exists (pb, PA, psz). split; [apply HL1; right; exact HPB| cbn; clear - Ha PB1 PB2; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma oinv_alloc : forall ΣX stX mX OWX boX NEW CX ΣY mY pn A n cst,
    oinv ΣX stX mX OWX boX NEW CX ->
    agree_on (aclient_addr (OWX ++ NEW ++ LB) spa) mX mY ->
    AHEAP ΣY ((pn, A, n) :: OWX) (NEW ++ LB) mY ->
    mem_inv ctasegs mY -> stk ctasegs mY lo spa ->
    rt_credit RT ΣX - cst <= rt_credit RT ΣY -> 0 <= cst <= CX ->
    oinv ΣY stX mY OWX boX ((pn, A, n) :: NEW) (CX - cst).
  Proof.
    kh. intros until cst. intros OI AG HEAPY MI ST CRY HC.
    destruct (AH_release _ _ _ _ _ HEAPY) as [HEAPY' OKb].
    pose proof OI as (_ & _ & _ & _ & _ & _ & _ & LBOK).
    eapply (oinv_heap ΣX stX mX OWX boX NEW CX ΣY mY (OWX ++ NEW ++ LB) ((pn, A, n) :: NEW) cst);
      [exact OI| eapply agree_on_mono; [exact AG| intros a [Ha _]; exact Ha]| intros b [Hb|Hb]; [apply in_app_iff; left; exact Hb| apply in_app_iff; right; apply in_app_iff; right; exact Hb]
      | cbn [app]; exact HEAPY'| constructor; [exact OKb| exact LBOK]| exact MI| exact ST| exact CRY| exact HC].
  Qed.

  (* [comment removed for export] *)
  Lemma oinv_allocX : forall ΣX stX mX OWX boX NEW CX ΣY mY pn A n cst,
    oinv ΣX stX mX OWX boX NEW CX ->
    agree_on (fun a => aclient_addr (OWX ++ NEW ++ LB) spa a /\ ~ rin_ivs XP a) mX mY ->
    AHEAP ΣY ((pn, A, n) :: OWX) (NEW ++ LB) mY ->
    mem_inv ctasegs mY -> stk ctasegs mY lo spa ->
    rt_credit RT ΣX - cst <= rt_credit RT ΣY -> 0 <= cst <= CX ->
    oinv ΣY stX mY OWX boX ((pn, A, n) :: NEW) (CX - cst).
  Proof.
    kh. intros until cst. intros OI AG HEAPY MI ST CRY HC.
    destruct (AH_release _ _ _ _ _ HEAPY) as [HEAPY' OKb].
    pose proof OI as (_ & _ & _ & _ & _ & _ & _ & LBOK).
    eapply (oinv_heap ΣX stX mX OWX boX NEW CX ΣY mY (OWX ++ NEW ++ LB) ((pn, A, n) :: NEW) cst);
      [exact OI| exact AG| intros b [Hb|Hb]; [apply in_app_iff; left; exact Hb| apply in_app_iff; right; apply in_app_iff; right; exact Hb]
      | cbn [app]; exact HEAPY'| constructor; [exact OKb| exact LBOK]| exact MI| exact ST| exact CRY| exact HC].
  Qed.

  (* [comment removed for export] *)
  Lemma oinv_call : forall ΣX stX mX OWX boX NEW CX,
    oinv ΣX stX mX OWX boX NEW CX ->
    AHEAP ΣX OWX (NEW ++ LB) mX /\ stk ctasegs mX lo spa /\ ACEIL <= lo /\ lo <= spa - STK
    /\ spa + 16 <= USTACK_TOP /\ spa mod 16 = 0
    /\ mem_inv ctasegs mX /\ crypto_statics mX /\ ap_state stX mX OWX E boX /\ 0 <= CX <= rt_credit RT ΣX
    /\ 0 <= FRM /\ Z.of_nat (length FR) + FRM <= Z.of_nat FRAMES_MAX.
  Proof.
    kh. intros until CX. intros (PREX & _).
    destruct PREX as (HEAP & AS & IDS & DC & ST0 & CEIL' & LOSP & TOP' & AL16 & MI0 & CRED & FRM').
    pose proof ESP as ESP. rewrite ESP in *. pose proof AS as (_ & (CS & _) & _).
    repeat (split; [first [assumption| (clear - LOSP; lia)| (clear - TOP' ; lia)| (clear - CRED; lia)| (clear - FRM'; lia)]|]). clear - FRM'; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma oinv_payload : forall ΣX stX mX OWX boX NEW CX,
    oinv ΣX stX mX OWX boX NEW CX -> 0 < D -> D + zlength c < 2 ^ 63 -> zlength c < 2 ^ 26 ->
    payload_okA mX (NEW ++ LB) D c.
  Proof.
    kh. intros until CX. intros OI D1 D63 D26. destruct OI as (_ & _ & _ & _ & _ & HB & _).
    split; [exact HB|]. split; [exact DF|]. split; [exact D1|]. split; [exact D63|]. split; [exact D26|].
    destruct PBX as [E0|(pb & PA & psz & H1 & H2 & H3)]; [left; exact E0| right].
    exists (pb, PA, psz). split; [apply in_app_iff; right; exact H1|]. cbn [blk_addr blk_size fst snd]. clear - H2 H3; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma oinv_after : forall ΣX stX mX OWX boX NEW CX ΣY stY mY OWY boY XX NEW2 cst,
    oinv ΣX stX mX OWX boX NEW CX ->
    ap_preA ΣY stY mY OWY (NEW2 ++ NEW ++ LB) E boY (Z_to_bv 64 spa) lo 0 0 0 ->
    ax_pres (NEW ++ LB) spa (XX ++ LIBW_A) mX mY ->
    (forall a, rin_ivs XX a -> (spa <= a < bv_unsigned sp) \/ rin_ivs XP a \/ (exists b, In b NEW /\ blk_addr b <= a < blk_addr b + blk_size b)) ->
    rt_credit RT ΣX - cst <= rt_credit RT ΣY -> 0 <= cst <= CX ->
    blocks_kept K stY OWY mX mY -> Forall lbokA NEW2 ->
    oinv ΣY stY mY OWY boY (NEW2 ++ NEW) (CX - cst).
  Proof.
    kh. intros until cst. intros OI PREY AXY HXX CRY HC (BK1 & BK2 & BK3) LBOK2. pose proof SPR as SPR. pose proof DLEN as DLEN.
    pose proof (oinv_facts _ _ _ _ _ _ _ OI) as (HEAP3 & ND3 & BND & FRSH & DJL & DJO).
    destruct OI as (PREX & AX & KO & KI & KP & HB & CR & LBOK).
    destruct PREX as (HEAP & _ & _ & _ & _ & _ & LOSP & _ & _ & _ & CRED & FRM').
    destruct PREY as (HEAPY & ASY & IDSY & DCY & STY & _ & _ & TOPY & AL16Y & MIY & _ & _).
    pose proof ESP as ESP. rewrite ESP in *.
    pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & _ & C3). unfold SEGTOP_A in C1.
    assert (XPF : forall iv, In iv XP -> exists b, In b LB /\ blk_addr b <= fst iv /\ snd iv <= blk_addr b + blk_size b)
      by (intros iv Hiv; exact (proj1 (Forall_forall _ _) XPok iv Hiv)).
    (* [comment removed for export] *)
    assert (CL : forall a, ax_client LB (bv_unsigned sp) X0 a -> ax_client (NEW ++ LB) spa (XX ++ LIBW_A) a).
    { intros a [HXa Hc]. split.
      - intros HIN. apply rin_ivs_app_iff in HIN. destruct HIN as [HIN|HIN]; [| apply HXa; apply rin_ivs_app_iff; right; exact HIN].
        destruct (HXX a HIN) as [Hs|[Hs|(b & Hb & Hr)]].
        + destruct Hc as [Hc|[Hc|(b & Hb & Hr)]]; [clear - Hs Hc; lia| pose proof (client_static_below a Hc); clear - H Hs C1 CEIL LOSP STK0; lia|].
          pose proof (BND b ltac:(apply in_app_iff; right; apply in_app_iff; right; exact Hb)) as (_ & _ & R3 & _). clear - Hs Hr R3 CEIL LOSP STK0. lia.
        + apply HXa. apply rin_ivs_app_iff. left. exact Hs.
        + assert (Hb' : In b (OWX ++ NEW ++ LB)) by (apply in_app_iff; right; apply in_app_iff; left; exact Hb).
          pose proof (BND b Hb') as (_ & _ & R3 & _).
          destruct Hc as [Hc|[Hc|(b' & Hb2 & Hr2)]]; [clear - Hc Hr R3 CEIL LOSP STK0 OFS0; lia
            | exact (blk_not_static ΣX OWX (NEW ++ LB) mX b a HEAP Hb' Hr Hc)|].
          pose proof (DJL b b' Hb Hb2). clear - H Hr Hr2. lia.
      - destruct Hc as [Hc|[Hc|(b & Hb & Hr)]]; [left; clear - Hc OFS0; lia| right; left; exact Hc| right; right; exists b; split; [apply in_app_iff; right; exact Hb| exact Hr]]. }
    split; [| split; [| split; [exact BK1| split; [| split; [| split; [| split; [clear - CR CRY HC; lia| apply Forall_app; split; [exact LBOK2| exact LBOK]]]]]]]].
    - unfold ap_preA. rewrite ESP, <- app_assoc. split; [exact HEAPY|]. split; [exact ASY|]. split; [exact IDSY|]. split; [exact DCY|].
      split; [exact STY|]. split; [exact CEIL|]. split; [exact LOSP|]. split; [exact TOPY|]. split; [exact AL16Y|]. split; [exact MIY|].
      split; [clear - CRED CRY HC; lia|].
      exact FRM'.
    - eapply ax_pres_trans; [exact AX|]. intros a Ha HC'. exact (AXY a Ha (CL a HC')).
    - intros b Hb Hin. apply in_app_iff in Hin. destruct Hin as [Hin|Hin]; [exact (BK2 b Hb Hin)|]. apply (KI b Hb). apply in_app_iff. right. exact Hin.
    - eapply kept_trans; [exact KP| exact BK3].
    - destruct PBX as [E0|(pb & PA & psz & HPB & PB1 & PB2)].
      { rewrite E0 in HB |- *. destruct HB as (HB0 & HB1 & _). split; [exact HB0|]. split; [exact HB1|]. intros i Hi. cbn in Hi. lia. }
      assert (HPB' : In (pb, PA, psz) (OWX ++ NEW ++ LB)) by (apply in_app_iff; right; apply in_app_iff; right; exact HPB).
      pose proof (BND _ HPB') as (_ & _ & P3 & P4). cbn [blk_addr blk_size fst snd] in P3, P4.
      eapply bytes_at_agree; [exact AXY| exact HB|]. intros a Ha. rewrite DLEN in Ha. split.
      + intros HIN. apply rin_ivs_app_iff in HIN. destruct HIN as [HIN|HIN].
        * destruct (HXX a HIN) as [Hs|[Hs|(b & Hb & Hr)]]; [clear - Hs Ha PB1 PB2 P3 CEIL LOSP STK0; lia| |].
          -- apply rin_ivs_In in Hs. destruct Hs as (iv & Hiv & Hr). pose proof (proj1 (Forall_forall _ _) XPD _ Hiv) as [E0|X1];
               [rewrite E0 in Ha; unfold zlength in Ha; cbn in Ha; clear - Ha; lia| clear - Ha Hr X1; lia].
          -- pose proof (DJL b (pb, PA, psz) Hb HPB) as DJ. cbn [blk_addr blk_size fst snd] in DJ. clear - Ha Hr DJ PB1 PB2. lia.
        * pose proof (libw_rangeA a HIN). clear - H Ha PB1 PB2 P4. lia.
      + right; right. exists (pb, PA, psz). split; [apply in_app_iff; right; exact HPB| cbn; clear - Ha PB1 PB2; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma oinv_perm : forall ΣX stX mX OWX boX NEW NEW' CX,
    Permutation NEW NEW' -> oinv ΣX stX mX OWX boX NEW CX -> oinv ΣX stX mX OWX boX NEW' CX.
  Proof.
    kh. intros until CX. intros P (PREX & AX & KO & KI & KP & HB & CR & LBOK).
    destruct PREX as (HEAP & REST).
    split; [| split; [exact AX| split; [exact KO| split; [exact KI| split; [exact KP| split; [exact HB| split; [exact CR| eapply Forall_perm; [exact P| exact LBOK]]]]]]]].
    split; [| exact REST]. eapply AH_lb_perm; [exact HEAP|]. apply Permutation_app_tail. exact P.
  Qed.

  (* [comment removed for export] *)
  Lemma oinv_credit : forall ΣX stX mX OWX boX NEW CX CX',
    oinv ΣX stX mX OWX boX NEW CX -> 0 <= CX' <= CX -> oinv ΣX stX mX OWX boX NEW CX'.
  Proof.
    kh. intros until CX'. intros (PREX & AX & KO & KI & KP & HB & CR & LBOK) HC.
    split; [| split; [exact AX| split; [exact KO| split; [exact KI| split; [exact KP| split; [exact HB| split; [clear - CR HC; lia| exact LBOK]]]]]]].
    pose proof PREX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & FRM').
    eapply ap_preA_weaken; [exact PREX| clear; lia| exact HC| clear - FRM'; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma pre_resp : forall ΣF stF mF OWF boF NEW CF,
    oinv ΣF stF mF OWF boF NEW CF -> stk ctasegs mF lo (bv_unsigned sp) ->
    ap_preA ΣF stF mF OWF (NEW ++ LB) E boF sp lo 0 0 0
    /\ ax_pres LB (bv_unsigned sp) X0 m mF
    /\ rt_credit RT Σ - CST <= rt_credit RT ΣF
    /\ blocks_kept K stF OWF m mF
    /\ (forall b, In b NEW -> ~ In (blk_id b) (map blk_id (OWF ++ LB)))
    /\ Forall lbokA NEW.
  Proof.
    kh. intros until CF. intros OI ST. pose proof (oinv_facts _ _ _ _ _ _ _ OI) as (_ & _ & _ & FRSH & _).
    destruct OI as (PREX & AX & KO & KI & KP & HB & CR & LBOK).
    destruct PREX as (HEAP & AS & IDS & DC & ST0 & CEIL' & LOSP & TOP' & AL16 & MI0 & CRED & FRM').
    split; [| split; [exact AX| split; [clear - CR CRED; lia| split; [split; [exact KO| split; [intros b Hb Hin; apply (KI b Hb); apply in_app_iff; left; exact Hin| exact KP]]| split; [exact FRSH| exact LBOK]]]]].
    unfold ap_preA. split; [exact HEAP|]. split; [exact AS|]. split; [exact IDS|]. split; [exact DC|]. split; [exact ST|]. split; [exact CEIL|].
    split; [clear - LO STK0 OFS0; lia|]. split; [exact TOP|]. split; [exact SP16|]. split; [exact MI0|].
    split; [clear - CRED; lia|]. clear - FRM'; lia.
  Qed.

  (* [comment removed for export] *)
  Definition ap_call_postA {A} (ra : word) (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (mX : mem) (NEW : list block) (CX cost : Z)
      (RES : A * ap_st bptr -> list block -> mem -> word -> Z * Z -> Prop) (r : A * ap_st bptr) (ΣY : rts RT) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (F' : bvmap 5 word) (fc' : bv 32) mY OWY boY,
      ms' = MS (mkR ra (Z_to_bv 64 spa) gp (wz TP_A) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F' (ret_pc ra) fc' None mY (seg_rom ctasegs)
      /\ oinv ΣY (snd r) mY OWY boY NEW (CX - cost)
      /\ ax_pres (NEW ++ LB) spa LIBW_A mX mY
      /\ RES r OWY mY a0 boY.

  Lemma oinv_ap_callA : forall {A} (entry stack cost frames : Z) ARGS (cst : ap_st bptr -> aprog bptr (A * ap_st bptr)) RES
      (ra gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (FX : bvmap 5 word) (fcX : bv 32)
      ΣX stX mX OWX boX NEW CX (ras' : list Z),
    ap_stmtA entry stack cost frames ARGS cst RES ->
    oinv ΣX stX mX OWX boX NEW CX -> stack <= STK -> 0 <= cost <= CX -> 0 <= frames <= FRM ->
    uw_chain USTACK_TOP mX spa (bv_unsigned s0) ras' -> uk_ctx entry (bv_unsigned ra :: ras') -> ras' <> nil ->
    ARGS stX OWX mX a0 a1 a2 a3 a4 a5 boX ->
    implAp (cst stX) ΣX (ap_call_postA ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 mX NEW CX cost RES)
      (MS (mkR ra (Z_to_bv 64 spa) gp (wz TP_A) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          FX (wz entry) fcX None mX (seg_rom ctasegs)).
  Proof.
    kh. intros until ras'. intros W OI LE HC HF UWc CTXc NEc HA. pose proof ESP as ESP.
    pose proof OI as (PREX & AX & KO & KI & KP & HB & CR & LBOK).
    pose proof PREX as (HEAP & _ & _ & _ & _ & _ & _ & _ & _ & _ & CRED & FRM').
    eapply implAp_mono.
    { unfold ap_stmtA in W. eapply W; [eapply ap_preA_weaken; [exact PREX| exact LE| clear - HC CRED; lia| clear - HF FRM'; lia]| reflexivity| rewrite ESP; exact UWc| exact CTXc| exact NEc| exact HA| exact KO| exact KI]. }
    intros r ΣY ms' PO. cbv beta in PO.
    destruct PO as (q0 & q1 & q2 & p0 & p1 & p2 & p3 & p4 & p5 & p6 & p7 & q3 & q4 & q5 & q6 & F' & fc' & mY & OWY & boY & -> & PREY & AXY & CRY & BKY & RESY).
    rewrite ESP in AXY.
    unfold ap_call_postA. exists q0, q1, q2, p0, p1, p2, p3, p4, p5, p6, p7, q3, q4, q5, q6, F', fc', mY, OWY, boY.
    split; [reflexivity|]. split; [| split; [exact AXY| exact RESY]].
    eapply (oinv_after _ _ _ _ _ NEW CX ΣY (snd r) mY OWY boY [] [] cost); [exact OI| cbn [app]; exact PREY| cbn [app]; exact AXY| intros a []| exact CRY| exact HC| exact BKY| constructor].
  Qed.
End Act.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma oinv_reframe : forall (sp : word) (m : mem) (Σ : rts RT) (LB : list block) (E : ap_env) (lo : Z) (K : list block)
    (c : list Z) (D : Z) (XP : list (Z * Z)) (spa STK CST FRM spa' STK' : Z) ΣX stX mX OWX boX NEW CX,
  oinv sp m Σ LB E lo K c D XP spa STK CST FRM ΣX stX mX OWX boX NEW CX ->
  bv_unsigned sp + 16 <= USTACK_TOP ->
  stk ctasegs mX lo spa' -> lo <= spa' - STK' -> spa' <= bv_unsigned sp -> 0 <= STK' -> spa' mod 16 = 0 ->
  oinv sp m Σ LB E lo K c D XP spa' STK' CST FRM ΣX stX mX OWX boX NEW CX.
Proof.
  intros until CX. intros (PREX & REST) TOP ST' LO' OFS0' STK0' OFS16'. split; [| exact REST].
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  destruct PREX as (HEAP & AS & IDS & DC & ST0 & CEIL' & LOSP & TOP' & AL16 & MI0 & CRED & FRM').
  pose proof ST' as (CL & _ & _).
  assert (E1 : bv_unsigned (Z_to_bv 64 spa') = spa') by (apply unsigned_lit; clear - SPR CL LO' STK0' OFS0'; lia).
  unfold ap_preA. rewrite E1. split; [exact HEAP|]. split; [exact AS|]. split; [exact IDS|]. split; [exact DC|]. split; [exact ST'|].
  split; [exact CEIL'|]. split; [exact LO'|]. split; [clear - TOP OFS0'; lia|].
  split; [exact OFS16'|].
  split; [exact MI0|]. split; [exact CRED| exact FRM'].
Qed.

(* [comment removed for export] *)
Lemma ap_preA_rebase : forall Σ st m OW LB E bo (sp : word) lo F STK CST FRM,
  ap_preA Σ st m OW LB E bo sp lo (F + STK) CST FRM -> 0 <= F -> F mod 16 = 0 -> 0 <= STK ->
  ap_preA Σ st m OW LB E bo (Z_to_bv 64 (bv_unsigned sp - F)) lo STK CST FRM.
Proof.
  intros until FRM. intros PRE F0 F16 STK0.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  destruct PRE as (HEAP & AS & IDS & DC & ST & CEIL' & LOSP & TOP' & AL16 & MI & CRED & FRM').
  pose proof ST as (CL & _ & _).
  destruct (stk_carve ctasegs m lo (bv_unsigned sp) (Z.to_nat F) ST ltac:(rewrite Z2Nat.id by lia; lia)) as [ST' _]. rewrite Z2Nat.id in ST' by lia.
  assert (E1 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp - F)) = bv_unsigned sp - F) by (apply unsigned_lit; clear - SPR CL LOSP F0 STK0; lia).
  unfold ap_preA. rewrite E1.
  split; [exact HEAP|]. split; [exact AS|]. split; [exact IDS|]. split; [exact DC|]. split; [exact ST'|].
  split; [exact CEIL'|]. split; [clear - LOSP; lia|]. split; [clear - TOP' F0; lia|].
  split; [clear - AL16 F16; rewrite Zminus_mod, AL16, F16; reflexivity|]. split; [exact MI|]. split; [exact CRED| exact FRM'].
Qed.

(* [comment removed for export] *)
Lemma oinv_xp : forall (sp : word) (m : mem) (Σ : rts RT) (LB : list block) (E : ap_env) (lo : Z) (K : list block)
    (c : list Z) (D : Z) (XP XP' : list (Z * Z)) (spa STK CST FRM : Z) ΣX stX mX OWX boX NEW CX,
  oinv sp m Σ LB E lo K c D XP spa STK CST FRM ΣX stX mX OWX boX NEW CX ->
  (forall iv, In iv XP -> In iv XP') ->
  oinv sp m Σ LB E lo K c D XP' spa STK CST FRM ΣX stX mX OWX boX NEW CX.
Proof.
  intros until CX. intros (PREX & AX & REST) INCL. split; [exact PREX|]. split; [| exact REST].
  intros a Ha [HX Hc]. apply (AX a Ha). split; [| exact Hc]. intros HIN. apply HX.
  apply rin_ivs_app_iff in HIN. apply rin_ivs_app_iff. destruct HIN as [HIN|HIN]; [left| right; exact HIN].
  apply rin_ivs_In in HIN. apply rin_ivs_In. destruct HIN as (iv & H1 & H2). exists iv. split; [apply INCL; exact H1| exact H2].
Qed.

(* [comment removed for export] *)
Lemma lbokA_pop : forall f k b, @lbokA (push AR f k) b -> @lbokA AR b.
Proof.
  intros f k b [H1 H2]. split; [exact H1|]. intros (f' & k' & Hin & R). apply H2. exists f', k'. split; [cbn [ar_FR push amb]; right; exact Hin| exact R].
Qed.

End WithRT.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma arr_repA_relistK : forall m L L' adr o,
  arr_repA m L adr o -> (forall b, In b (CtSctP.W_sct_list_free.oblk adr o) -> In b L') -> arr_repA m L' adr o.
Proof.
  intros m L L' adr [[q n]|] H HI; cbn in *; [| exact I]. destruct H as (H1 & H2 & H3). split; [exact H1|]. split; [apply HI; left; reflexivity| exact H3].
Qed.

Lemma sct_repA_relistK : forall m L L' adr s,
  sct_repA m L adr s -> (forall b, In b (CtSctP.W_sct_list_free.sct_blocks adr s) -> In b L') -> sct_repA m L' adr s.
Proof.
  intros m L L' adr s (H1 & AL & H2 & H3 & H4 & H5 & H6 & H7) HI. unfold CtSctP.W_sct_list_free.sct_blocks in HI.
  split; [apply HI; rewrite !in_app_iff; do 4 right; left; reflexivity|]. split; [exact AL|]. split; [exact H2|].
  split; [eapply arr_repA_relistK; [exact H3|]; intros b Hb; apply HI; rewrite !in_app_iff; tauto|].
  split; [eapply arr_repA_relistK; [exact H4|]; intros b Hb; apply HI; rewrite !in_app_iff; tauto|].
  split; [eapply arr_repA_relistK; [exact H5|]; intros b Hb; apply HI; rewrite !in_app_iff; tauto|].
  split; [eapply arr_repA_relistK; [exact H6|]; intros b Hb; apply HI; rewrite !in_app_iff; tauto| exact H7].
Qed.

Lemma arr_repA_agreeK : forall P m m' L adr o,
  agree_on P m m' -> (forall q n a, o = Some (q, n) -> adr q <= a < adr q + n -> P a) -> arr_repA m L adr o -> arr_repA m' L adr o.
Proof.
  intros P m m' L adr [[q n]|] AG HP H; cbn in *; [| exact I]. destruct H as (Hn & HL & bs & HB). split; [exact Hn|]. split; [exact HL|]. exists bs.
  eapply rw_cells_agree; [exact AG| exact HB|]. intros a Ha. cbn in Ha. rewrite Nat.add_0_r, Z2Nat.id in Ha by lia. eapply HP; [reflexivity| lia].
Qed.

Lemma sct_repA_agreeK : forall P m m' L adr s,
  agree_on P m m' -> (forall b a, In b (CtSctP.W_sct_list_free.sct_blocks adr s) -> blk_addr b <= a < blk_addr b + blk_size b -> P a) ->
  sct_repA m L adr s -> sct_repA m' L adr s.
Proof.
  intros P m m' L adr s AG HP (H1 & AL & H2 & H3 & H4 & H5 & H6 & REST).
  assert (BL : forall b, (In b (CtSctP.W_sct_list_free.oblk adr (osz32 (sc_logid s))) \/ In b (CtSctP.W_sct_list_free.oblk adr (sc_ext s))
                          \/ In b (CtSctP.W_sct_list_free.oblk adr (sc_sig s)) \/ In b (CtSctP.W_sct_list_free.oblk adr (sc_blob s))
                          \/ b = (sc_blk s, adr (sc_blk s), SCT_SIZE)) -> In b (CtSctP.W_sct_list_free.sct_blocks adr s)).
  { intros b Hb. unfold CtSctP.W_sct_list_free.sct_blocks. rewrite !in_app_iff. cbn. destruct Hb as [Hb|[Hb|[Hb|[Hb| ->]]]]; tauto. }
  split; [exact H1|]. split; [exact AL|]. split.
  { eapply rw_cells_agree; [exact AG| exact H2|]. intros a Ha. apply (HP (sc_blk s, adr (sc_blk s), SCT_SIZE)); [apply BL; right; right; right; right; reflexivity|].
    cbn. rewrite CtSctP.SctRep.sct_cells_size in Ha. unfold SCT_SIZE in *. lia. }
  split; [eapply arr_repA_agreeK; [exact AG| intros q n a Ho Ha; apply (HP (q, adr q, n)); [apply BL; left; rewrite Ho; left; reflexivity| cbn; lia]| exact H3]|].
  split; [eapply arr_repA_agreeK; [exact AG| intros q n a Ho Ha; apply (HP (q, adr q, n)); [apply BL; right; left; rewrite Ho; left; reflexivity| cbn; lia]| exact H4]|].
  split; [eapply arr_repA_agreeK; [exact AG| intros q n a Ho Ha; apply (HP (q, adr q, n)); [apply BL; right; right; left; rewrite Ho; left; reflexivity| cbn; lia]| exact H5]|].
  split; [eapply arr_repA_agreeK; [exact AG| intros q n a Ho Ha; apply (HP (q, adr q, n)); [apply BL; right; right; right; left; rewrite Ho; left; reflexivity| cbn; lia]| exact H6]|].
  exact REST.
Qed.
