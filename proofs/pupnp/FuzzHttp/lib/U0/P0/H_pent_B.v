(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From stdpp Require Import base list.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac Image Arr.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Top Require Import AllocIF AllocSpec SReach.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac HttpAlloc HttpAllocX CellConv.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Segs F_syscalls F_memmove H_scanner_get_token H_vfmatch_A H_vfmatch_G3 H_match H_obj H_membuffer_assign H_membuffer_delete
     H_UpnpPrintf H_entity_read_method H_prep H_presp_B H_presp_C.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import H_pent_A H_pent_M.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Ceiling.
Import ListNotations.
Open Scope Z_scope.
Set Printing Width 1000.
Set Printing Depth 100.

Lemma disjoint_from_Forall : forall (W : list ivl) X n,
  Forall (fun iv => snd iv <= X \/ X + n <= fst iv)%Z W -> disjoint_from W X n.
Proof.
  induction W as [|[l h] W IH]; intros X n F; cbn; [exact I|].
  inversion F as [|? ? Hiv F']; subst. cbn in Hiv. split; [lia| apply IH; exact F'].
Qed.

Definition pmod8 (x : Z) : Prop := (x mod 8 = 0)%Z.

Section W.
Context {HCEIL : HasCeiling}.
  Variable AI : alloc_if rsegs.
  Variable AC : alloc_contracts AI.
  Notation L_ := (ai_L rsegs AI).
  Notation K := (ai_K rsegs AI).
  Notation BLK := (block K).
  Notation hdr := (hdr AI).
  Hypothesis LOK : layout_ok AI.
  Hypothesis REALLOCPC : al_realloc_pc L_ = 0x1995c.
  Hypothesis TPV : al_tp L_ = 0x3b820.
  Hypothesis ERRNOV : al_errno L_ = 0x3b77c.
  Hypothesis CAN : canary_ok AI.
  Hypothesis ERRNC : forall lo hi, al_client_static L_ lo hi -> hi <= al_errno L_ \/ al_errno L_ + 4 <= lo.
  Hypothesis BLK4096 : blk4096_ok AI.
  Hypothesis BLKIMG : blk_img_ok AI.
  Hypothesis GERM : germ_stmt AI.

  Hypothesis GMST : exists lo hi, al_client_static L_ lo hi /\ lo <= GMAXA /\ GMAXA + 8 <= hi.
  Hypothesis IWST : exists lo hi, al_client_static L_ lo hi /\ lo <= INITWASCALLED /\ INITWASCALLED + 1 <= hi.

  Variables (PHS : mem -> Prop) (TABA ZEROA : Z).
  Hypothesis PHS_munch : forall W m m', munch W m m' -> wmono rsegs m m' -> disjoint_from W TABA 528 -> disjoint_from W ZEROA 1 -> PHS m -> PHS m'.
  Hypothesis PHS_hp : forall (LB : list BLK) SP m m', heap_pres AI LB SP m m' -> PHS m -> PHS m'.
  Hypothesis TABST : exists lo hi, al_client_static L_ lo hi /\ lo <= TABA /\ TABA + 528 <= hi.
  Hypothesis ZST : exists lo hi, al_client_static L_ lo hi /\ lo <= ZEROA /\ ZEROA + 1 <= hi.

  Variables (P q lo B gmax : Z) (LBK : list BLK) (isreq maj min rm sc : Z) (m0 : mem).
  Variables (ra s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e : word).
  Notation S := (P + 480)%Z.
  Notation MB := (P + 400)%Z.
  Hypothesis QLO : (lo + 2432 <= q)%Z.
  Hypothesis QLO2 : (lo <= q - 32 - al_stack L_)%Z.
  Hypothesis STK0 : (0 <= al_stack L_)%Z.
  Hypothesis LO0 : (0x5d000 <= lo)%Z.
  Hypothesis CEIL : (alloc_ceiling <= lo)%Z.
  Hypothesis QP : (q + 144 <= P)%Z.
  Hypothesis PB : (P + 504 <= B)%Z.
  Hypothesis BHI : (B < 2^62)%Z.
  Hypothesis GMX : (0 < gmax < 2^32)%Z.
  Hypothesis P8 : pmod8 P.
  Hypothesis Q8 : pmod8 q.

  #[using="B PB BHI"] Lemma PHI63 : (P + 504 < 2^63)%Z. Proof. lia. Qed.
  #[using="QLO"] Lemma QLO1 : (lo <= q)%Z. Proof. lia. Qed.

  Notation PRS pc x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2v s7 t3 t4 t5 t6 gp F fc m :=
    (MS (mkR x1 (wz q) gp (wz (al_tp L_)) t0 t1 t2 (wz P) (wz MB) a0 a1 a2 a3 a4 a5 a6 a7 s2v (wz FMT_CHUNK) (wz JT_ENT) (wz GMAXA) (wz FMT_CRLF) s7 (wz 5) (wz 6) (wz 4) (wz 4294967295) t3 t4 t5 t6)
        F (wz pc) fc None m (seg_rom rsegs)).

  Definition WE : list ivl := [(P + 4, P + 8); (P + 288, P + 432); (P + 440, P + 480); (P + 488, P + 496)]%Z.

  Definition ent_ok (entp cur esp csz : Z) (elw : word) : Prop :=
    (2 <= entp -> esp <= cur)
    /\ (entp = 3 \/ entp = 5 -> exists elen, elw = wz elen /\ 0 <= elen <= gmax)
    /\ (entp = 5 -> 1 <= csz <= gmax /\ csz < 2^31).

  Definition elen_of (elw : word) : Z := bv_unsigned elw.

  Definition pe_meas (entp : Z) (elw : word) : Z :=
    if (entp =? 1)%Z then 4 * gmax + 10
    else if (entp =? 3)%Z then 2 * (gmax - elen_of elw) + 3
    else if (entp =? 5)%Z then 2 * (gmax - elen_of elw) + 2
    else 0.

  Definition PI (s : ai_PS rsegs AI) (LB : list BLK) (m : mem) (cur A len cap : Z) (okm : option K) (bs : list byte)
      (ebw elw : word) (err hack pos entp clen csz esp : Z) (ns : list (BLK * Z)) (hs : list hdr) (X meth : Z) : Prop :=
    RHEAP rsegs AI s LB m /\ RENV rsegs AI m B /\ mem_inv rsegs m /\ stk rsegs m lo q
    /\ (exists e, rw_cells rsegs m (al_errno L_) [C4 e])
    /\ rw_cells rsegs m (q + 40) (peFS ra s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e) /\ peFX q m
    /\ p_scan m P cur /\ p_msg AI m LB P A len cap okm bs /\ (0 <= cur <= len)%Z
    /\ p_ent m P ebw elw /\ p_ctl m P err hack pos entp clen csz esp /\ p_hlist AI m P ns hs X /\ (X + 2 * (len - cur) <= VMAX)%Z
    /\ p_meth m P meth /\ p_ver m P isreq maj min /\ p_rs m P rm sc
    /\ bsub AI (hl_blocks AI ns hs ++ okb AI okm A cap ++ LBK) LB /\ NoDup (map blk_id (hl_blocks AI ns hs ++ okb AI okm A cap ++ LBK))
    /\ rw_cells rsegs m GMAXA [C8 (wz gmax)] /\ rw_cells rsegs m INITWASCALLED [C1 (Z_to_bv 8 0)]
    /\ hpx AI WE LBK (q + 144) m0 m /\ PHS m
    /\ ent_ok entp cur esp csz elw.

  Definition pent_post (gp : word) (F : bvmap 5 word) (fc : bv 32) : ai_PS rsegs AI -> list BLK -> machine_state -> Prop :=
    fun s' LB' ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (r cur' A' len' cap' : Z) (okm' : option K) (bs' : list byte)
        (ebw' elw' : word) (err' hack' pos' entp' clen' csz' esp' X' meth' : Z) (ns' : list (BLK * Z)) (hs' : list hdr),
      ms' = MS (mkR ra (wz (q + 144)) gp (wz (al_tp L_)) t0 t1 t2 s0e s1e (wz r) a1 a2 a3 a4 a5 a6 a7 s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom rsegs)
      /\ mem_inv rsegs m' /\ stk rsegs m' lo (q + 144) /\ RENV rsegs AI m' B
      /\ (exists e, rw_cells rsegs m' (al_errno L_) [C4 e])
      /\ hpx AI WE LBK (q + 144) m0 m'
      /\ RHEAP rsegs AI s' LB' m'
      /\ p_scan m' P cur' /\ p_msg AI m' LB' P A' len' cap' okm' bs' /\ (0 <= cur' <= len')%Z
      /\ p_ent m' P ebw' elw' /\ p_ctl m' P err' hack' pos' entp' clen' csz' esp' /\ p_hlist AI m' P ns' hs' X' /\ (X' <= VMAX)%Z
      /\ p_meth m' P meth' /\ p_ver m' P isreq maj min /\ p_rs m' P rm sc
      /\ bsub AI (hl_blocks AI ns' hs' ++ okb AI okm' A' cap' ++ LBK) LB' /\ NoDup (map blk_id (hl_blocks AI ns' hs' ++ okb AI okm' A' cap' ++ LBK))
      /\ rw_cells rsegs m' GMAXA [C8 (wz gmax)] /\ rw_cells rsegs m' INITWASCALLED [C1 (Z_to_bv 8 0)]
      /\ (0 <= r <= 5 /\ r <> 4)%Z.

  Definition hdrs_arm : Prop :=
    forall s LB m cur A len cap okm bs ebw elw err hack pos entp clen csz esp ns hs X meth gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 t3 t4 t5 t6 x1 (F : bvmap 5 word) fc,
      PI s LB m cur A len cap okm bs ebw elw err hack pos entp clen csz esp ns hs X meth -> entp = 6 ->
      SREACH AI (pent_post gp F fc) (PRS 0x15968 x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (wz S) s7 t3 t4 t5 t6 gp F fc m) s LB.

  Ltac fw := repeat apply Forall_cons; try apply Forall_nil; unfold WE, inside; cbn; repeat split; lia.

  Ltac open_PI H :=
    destruct H as (HR & HE & MI & ST & [errv ERR] & FSH & FX & PSC & PMSG & CUR & PENT & PCTL & PHL & XV & PMETH & PVER & PRS_ & BSUB & ND & GM & IW & HPX & PH & EOK).

  Definition PC (s : ai_PS rsegs AI) (LB : list BLK) (m : mem) (A len cap : Z) (okm : option K) (bs : list byte)
      (ebw elw : word) (err hack pos entp clen csz esp : Z) (ns : list (BLK * Z)) (hs : list hdr) (X meth scur xb : Z) : Prop :=
    RHEAP rsegs AI s LB m /\ RENV rsegs AI m B /\ mem_inv rsegs m /\ stk rsegs m lo q
    /\ (exists e, rw_cells rsegs m (al_errno L_) [C4 e])
    /\ rw_cells rsegs m (q + 40) (peFS ra s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e) /\ peFX q m
    /\ p_scan m P scur /\ p_msg AI m LB P A len cap okm bs
    /\ p_ent m P ebw elw /\ p_ctl m P err hack pos entp clen csz esp /\ p_hlist AI m P ns hs X /\ (0 <= xb <= len /\ X + 2 * (len - xb) <= VMAX)%Z
    /\ p_meth m P meth /\ p_ver m P isreq maj min /\ p_rs m P rm sc
    /\ bsub AI (hl_blocks AI ns hs ++ okb AI okm A cap ++ LBK) LB /\ NoDup (map blk_id (hl_blocks AI ns hs ++ okb AI okm A cap ++ LBK))
    /\ rw_cells rsegs m GMAXA [C8 (wz gmax)] /\ rw_cells rsegs m INITWASCALLED [C1 (Z_to_bv 8 0)]
    /\ hpx AI WE LBK (q + 144) m0 m /\ PHS m.

  Ltac open_PC H :=
    destruct H as (HR & HE & MI & ST & [errv ERR] & FSH & FX & PSC & PMSG & PENT & PCTL & PHL & XV & PMETH & PVER & PRS_ & BSUB & ND & GM & IW & HPX & PH).

  #[using="Type"] Lemma PI_PC : forall s LB m cur A len cap okm bs ebw elw err hack pos entp clen csz esp ns hs X meth,
    PI s LB m cur A len cap okm bs ebw elw err hack pos entp clen csz esp ns hs X meth ->
    PC s LB m A len cap okm bs ebw elw err hack pos entp clen csz esp ns hs X meth cur cur /\ (0 <= cur <= len)%Z /\ ent_ok entp cur esp csz elw.
  Proof.
    intros until meth. intros H. open_PI H. split; [| split; [exact CUR| exact EOK]].
    repeat (split; [first [eassumption| eexists; eassumption| lia]|]). exact PH.
  Qed.

  #[using="Type"] Lemma PC_PI : forall s LB m cur A len cap okm bs ebw elw err hack pos entp clen csz esp ns hs X meth xb,
    PC s LB m A len cap okm bs ebw elw err hack pos entp clen csz esp ns hs X meth cur xb -> (0 <= cur <= len)%Z -> (xb <= cur)%Z -> ent_ok entp cur esp csz elw ->
    PI s LB m cur A len cap okm bs ebw elw err hack pos entp clen csz esp ns hs X meth.
  Proof. intros until xb. intros H CUR XB EOK0. open_PC H. repeat (split; [first [eassumption| eexists; eassumption| lia]|]). exact EOK0. Qed.

  Definition hdrs_call : Prop := forall gp (F : bvmap 5 word) fc s LB m A len cap km bs ebw elw err hack pos entp clen csz esp ns hs X meth scur (rpc : Z)
      t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2v s7 t3 t4 t5 t6,
    PC s LB m A len cap (Some km) bs ebw elw err hack pos entp clen csz esp ns hs X meth scur scur -> (0 <= scur <= len)%Z ->
    ret_pc (wz rpc) = wz rpc ->
    (forall s' LB' m' (r cur' meth' err' pos' X' : Z) ns' hs' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
        PC s' LB' m' A len cap (Some km) bs ebw elw err' hack pos' entp clen csz esp ns' hs' X' meth' cur' cur' ->
        (0 <= r <= 5)%Z -> (scur <= cur' <= len)%Z ->
        SREACH AI (pent_post gp F fc) (PRS rpc (wz rpc) t0' t1' t2' (wz r) a1' a2' a3' a4' a5' a6' a7' s2v s7 t3' t4' t5' t6' gp F fc m') s' LB') ->
    SREACH AI (pent_post gp F fc) (PRS 0x14c4c (wz rpc) t0 t1 t2 (wz P) a1 a2 a3 a4 a5 a6 a7 s2v s7 t3 t4 t5 t6 gp F fc m) s LB.
  Hypothesis HCALL : hdrs_call.

  #[using="TPV QLO"] Lemma pe_exitC : forall s LB m cur A len cap okm bs ebw elw err hack pos entp clen csz esp ns hs X meth xb (r : Z)
      gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2v s7 t3 t4 t5 t6 x1 (F : bvmap 5 word) fc,
    PC s LB m A len cap okm bs ebw elw err hack pos entp clen csz esp ns hs X meth cur xb -> (0 <= cur <= len)%Z -> (0 <= r <= 5)%Z -> r <> 4 ->
    SREACH AI (pent_post gp F fc) (PRS 0x15a58 x1 t0 t1 t2 (wz r) a1 a2 a3 a4 a5 a6 a7 s2v s7 t3 t4 t5 t6 gp F fc m) s LB.
  Proof.
    intros until fc. intros INV CUR RR R4. open_PC INV.
    eapply sreach_evt. { rewrite TPV. eapply (pe_epi q lo QLO1); try eassumption. }
    intros ms' [-> ST']. apply sreach_ret. unfold pent_post.
    do 15 eexists. exists r, cur, A, len, cap, okm, bs, ebw, elw, err, hack, pos, entp, clen, csz, esp, X, meth, ns, hs.
    split; [rewrite TPV; reflexivity|]. repeat (split; [first [eassumption| eexists; eassumption| lia]|]). lia.
  Qed.

  #[using="TPV QLO"] Lemma pe_exit : forall s LB m cur A len cap okm bs ebw elw err hack pos entp clen csz esp ns hs X meth (r : Z)
      gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2v s7 t3 t4 t5 t6 x1 (F : bvmap 5 word) fc,
    PI s LB m cur A len cap okm bs ebw elw err hack pos entp clen csz esp ns hs X meth -> (0 <= r <= 5)%Z -> r <> 4 ->
    SREACH AI (pent_post gp F fc) (PRS 0x15a58 x1 t0 t1 t2 (wz r) a1 a2 a3 a4 a5 a6 a7 s2v s7 t3 t4 t5 t6 gp F fc m) s LB.
  Proof.
    intros until fc. intros INV RR R4. destruct (PI_PC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ INV) as (PCI & CUR & _).
    eapply pe_exitC; [exact PCI| exact CUR| exact RR| exact R4].
  Qed.

  #[using="BLK4096 BLKIMG"] Lemma msg_facts : forall s LB m A len cap okm bs, RHEAP rsegs AI s LB m -> p_msg AI m LB P A len cap okm bs ->
    (0 <= len <= cap)%Z /\ (cap + 1 <= LMAX)%Z /\ (0 <= A)%Z /\ (A + (cap + 1) <= alloc_ceiling)%Z
    /\ (forall km, okm = Some km -> In (km, A, cap + 1)%Z LB /\ rw_cells rsegs m A [CB (Z.to_nat (cap + 1)) bs] /\ 4096 <= A /\ (A + (cap + 1) <= 0x2a000 \/ 0x5d000 <= A))%Z
    /\ (okm = None -> A = 0 /\ len = 0 /\ cap = 0).
  Proof.
    intros s LB m A len cap okm bs HR (MBC & OWN & HL & HC & NULM). unfold LMAX in *.
    pose proof alloc_ceiling_bounds as CE. pose proof alloc_ceiling_aligned8 as CE8.
    destruct okm as [km|]; cbn in OWN.
    - destruct OWN as [HIN BLK]. destruct (ai_block_range rsegs AI _ _ _ _ HR HIN) as (R1 & R2 & R3 & R4 & _). cbn in R1, R4.
      pose proof (BLK4096 _ _ _ _ HR HIN) as R5. cbn in R5. pose proof (BLKIMG _ _ _ _ HR HIN) as R6. cbn in R6.
      split; [lia|]. split; [unfold LMAX; lia|]. split; [lia|]. split; [lia|]. split; [| intros; discriminate].
      intros km' E. injection E as <-. split; [exact HIN|]. split; [exact BLK|]. lia.
    - destruct OWN as (-> & -> & ->). cbn in NULM. split; [lia|]. split; [unfold LMAX; lia|]. split; [lia|]. split; [lia|].
      split; [intros; discriminate| intros _; repeat split; lia].
  Qed.

  Definition HI64 : Z := 2^64.
  #[using="LOK CEIL"] Lemma seg_heap_pres : forall s LB0 m1 (LBh : list BLK) W m m',
    RHEAP rsegs AI s LB0 m1 -> (forall b, In b LBh -> In b LB0) ->
    munch W m m' -> wmono rsegs m m' -> Forall (fun iv => lo <= fst iv) W ->
    heap_pres AI LBh HI64 m m'.
  Proof.
    intros s LB0 m1 LBh W m m' HR SUB MU WM FW a Ha Hc. split; [| intros Hw; apply WM; exact Hw].
    unfold munch in MU. pose proof (MU (wa a)) as E. unfold wa in E. rewrite unsigned_lit in E by lia. apply E.
    apply outside_of_forall. eapply Forall_impl; [| exact FW]. cbn. intros [l' h'] Hl; cbn in *.
    destruct Hc as [Hc|[(slo & shi & Hst & Hr)|(b & Hb & Hr)]].
    - unfold HI64 in Hc. lia.
    - destruct (lo_static_img rsegs AI LOK slo shi Hst) as (w & Hw & W1 & W2). pose proof (lo_img_ceiling rsegs AI LOK w Hw). lia.
    - destruct (ai_block_range rsegs AI _ _ _ _ HR (SUB b Hb)) as (_ & _ & _ & R4 & _). lia.
  Qed.

  #[using="Type"] Lemma pe_hlist_pres : forall m m' W (LBh : list BLK) SPx ns hs X,
    p_hlist AI m P ns hs X -> munch W m m' -> wmono rsegs m m' -> disjoint_from W (P + 288) 96 ->
    heap_pres AI LBh SPx m m' -> bsub AI (hl_blocks AI ns hs) LBh -> p_hlist AI m' P ns hs X.
  Proof.
    intros m m' W LBh SPx ns hs X (LC & FLC & FF & DL & HS & IT & HB & NB & X0') MU WM DJ HP SUB.
    unfold hl_blocks in SUB. apply (bsub_app AI) in SUB. destruct SUB as [S1 S2].
    split. { eapply rw_cells_transport; [exact LC| exact MU| exact WM|]. eapply disjoint_from_sub; [exact DJ| lia| cbn; lia]. }
    split. { eapply rw_cells_transport; [exact FLC| exact MU| exact WM|]. eapply disjoint_from_sub; [exact DJ| lia| cbn; lia]. }
    split. { eapply rw_cells_transport; [exact FF| exact MU| exact WM|]. eapply disjoint_from_sub; [exact DJ| lia| cbn; lia]. }
    split. { eapply (dlseg_heap_pres AI); [exact DL| exact HP|]. intros b it H. apply S1. exact (in_map fst _ _ H). }
    split. { eapply (hdrs_mem_heap_pres AI); [exact HS| exact HP| exact S2]. }
    auto.
  Qed.

  #[using="Type"] Lemma pe_msg_pres : forall m m' W (LBh LB LB' : list BLK) SPx A len cap okm bs,
    p_msg AI m LB P A len cap okm bs -> munch W m m' -> wmono rsegs m m' -> disjoint_from W (P + 400) 32 ->
    heap_pres AI LBh SPx m m' -> bsub AI (okb AI okm A cap) LBh -> (forall b, In b (okb AI okm A cap) -> In b LB') ->
    p_msg AI m' LB' P A len cap okm bs.
  Proof.
    intros m m' W LBh LB LB' SPx A len cap okm bs (MBC & OWN & HL & HC & NUL) MU WM DJ HP SUB SUB'.
    split. { eapply rw_cells_transport; [exact MBC| exact MU| exact WM|]. exact DJ. }
    split.
    { destruct okm as [k|]; cbn in OWN |- *; [| exact OWN]. destruct OWN as [HIN BLK]. split; [apply SUB'; left; reflexivity|].
      pose proof BLK as BLK'. destruct BLK' as [[W0 _] _].
      eapply (heap_pres_rw_cells rsegs AI); [exact HP| exact BLK|]. eapply client_range_block; [apply SUB; left; reflexivity| cbn; lia|].
      cbn [cells_size csize Nat.add blk_addr blk_size fst snd]. cbn in W0. lia. }
    auto.
  Qed.

  #[using="LOK TABA ZEROA PHS_munch TABST ZST lo QLO CEIL QP PB GMX"] Lemma PI_seg : forall s LB m m' W A len cap okm bs ns hs X meth,
    RHEAP rsegs AI s LB m -> RENV rsegs AI m B -> hpx AI WE LBK (q + 144) m0 m ->
    bsub AI (hl_blocks AI ns hs ++ okb AI okm A cap ++ LBK) LB ->
    munch W m m' -> wmono rsegs m m' ->
    Forall (fun iv => q + 144 <= fst iv /\ snd iv <= P + 504 /\ inside WE (fst iv) (snd iv - fst iv)
                      /\ (snd iv <= P + 288 \/ P + 384 <= fst iv) /\ (snd iv <= P + 400 \/ P + 432 <= fst iv)
                      /\ (snd iv <= P + 224 \/ P + 232 <= fst iv) /\ (snd iv <= P + 264 \/ P + 288 <= fst iv) /\ P + 8 <= fst iv) W ->
    rw_cells rsegs m (q + 40) (peFS ra s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e) -> peFX q m ->
    p_msg AI m LB P A len cap okm bs -> p_hlist AI m P ns hs X -> p_meth m P meth -> p_ver m P isreq maj min -> p_rs m P rm sc ->
    rw_cells rsegs m GMAXA [C8 (wz gmax)] -> rw_cells rsegs m INITWASCALLED [C1 (Z_to_bv 8 0)] -> PHS m ->
    RHEAP rsegs AI s LB m' /\ RENV rsegs AI m' B /\ hpx AI WE LBK (q + 144) m0 m'
    /\ rw_cells rsegs m' (q + 40) (peFS ra s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e) /\ peFX q m'
    /\ p_msg AI m' LB P A len cap okm bs /\ p_hlist AI m' P ns hs X /\ p_meth m' P meth /\ p_ver m' P isreq maj min /\ p_rs m' P rm sc
    /\ rw_cells rsegs m' GMAXA [C8 (wz gmax)] /\ rw_cells rsegs m' INITWASCALLED [C1 (Z_to_bv 8 0)] /\ PHS m'.
  Proof.
    intros s LB m m' W A len cap okm bs ns hs X meth HR HE HP BSUB MU WM FW FSH FX PMSG PHL PMETH PVER PRS_ GM IW PH0.
    pose proof alloc_ceiling_bounds as CE. pose proof alloc_ceiling_aligned8 as CE8.
    destruct (proj1 (bsub_app AI _ _ _) BSUB) as [SUBH BSUB2]. destruct (proj1 (bsub_app AI _ _ _) BSUB2) as [SUBM SUBK].
    assert (DJ : forall X0 n, (q <= X0)%Z -> Forall (fun iv => snd iv <= X0 \/ X0 + Z.of_nat n <= fst iv)%Z W -> disjoint_from W X0 (Z.of_nat n)).
    { intros X0 n HX F0. apply disjoint_from_Forall. exact F0. }
    assert (FWlo : Forall (fun iv => lo <= fst iv) W) by (eapply Forall_impl; [| exact FW]; cbn; intros [l' h'] X0; cbn in *; lia).
    assert (SUBHM : forall b, In b (hl_blocks AI ns hs ++ okb AI okm A cap) -> In b LB).
    { intros b Hb. apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [exact (SUBH b Hb)| exact (SUBM b Hb)]. }
    pose proof (seg_heap_pres s LB m _ W m m' HR SUBHM MU WM FWlo) as HPh.
    split. { eapply (ai_heap_frame rsegs AI); [exact HR| exact MU| exact WM|]. eapply Forall_impl; [| exact FW]. cbn. intros [l' h'] X0; cbn in *. left. lia. }
    split. { eapply (ai_env_frame rsegs AI); [exact HR| exact HE| exact MU| exact WM|]. eapply Forall_impl; [| exact FW]. cbn. intros [l' h'] X0; cbn in *. left. lia. }
    split. { eapply (hpx_trans rsegs AI); [exact HP|]. eapply (hpx_seg rsegs AI); [exact LOK| exact HR| exact SUBK| exact MU| exact WM|].
             eapply Forall_impl; [| exact FW]. cbn. intros [l' h'] X0; cbn in *. right; right. LiaTuning.ctauto. }
    split. { eapply rw_cells_transport; [exact FSH| exact MU| exact WM|]. unfold peFS. cbn [cells_size csize Nat.add].
             apply (DJ (q + 40)%Z 104%nat); [lia|]. eapply Forall_impl; [| exact FW]. cbn. intros [l' h'] X0; cbn in *. lia. }
    split. { destruct FX as (Q0 & [j16 Q16] & [cz Q20] & (da & db & Q24)).
             assert (D40 : disjoint_from W q 40). { apply (DJ q 40%nat); [lia|]. eapply Forall_impl; [| exact FW]. cbn. intros [l' h'] X0; cbn in *. lia. }
             split. { eapply rw_cells_transport; [exact Q0| exact MU| exact WM|]. eapply disjoint_from_sub; [exact D40| lia| cbn; lia]. }
             split. { eexists. eapply rw_cells_transport; [exact Q16| exact MU| exact WM|]. eapply disjoint_from_sub; [exact D40| lia| cbn; lia]. }
             split. { eexists. eapply rw_cells_transport; [exact Q20| exact MU| exact WM|]. eapply disjoint_from_sub; [exact D40| lia| cbn; lia]. }
             do 2 eexists. eapply rw_cells_transport; [exact Q24| exact MU| exact WM|]. eapply disjoint_from_sub; [exact D40| lia| cbn; lia]. }
    split. { eapply pe_msg_pres; [exact PMSG| exact MU| exact WM| | exact HPh| | intros b Hb; exact (SUBM b Hb)].
             - apply (DJ (P + 400)%Z 32%nat); [lia|]. eapply Forall_impl; [| exact FW]. cbn. intros [l' h'] X0; cbn in *. lia.
             - intros b Hb. apply in_or_app. right. exact Hb. }
    split. { eapply pe_hlist_pres; [exact PHL| exact MU| exact WM| | exact HPh|].
             - apply (DJ (P + 288)%Z 96%nat); [lia|]. eapply Forall_impl; [| exact FW]. cbn. intros [l' h'] X0; cbn in *. lia.
             - intros b Hb. apply in_or_app. left. exact Hb. }
    split. { destruct PMETH as [MC MR]. split; [| exact MR]. eapply rw_cells_transport; [exact MC| exact MU| exact WM|]. cbn [cells_size csize Nat.add].
             apply (DJ P 8%nat); [lia|]. eapply Forall_impl; [| exact FW]. cbn. intros [l' h'] X0; cbn in *. lia. }
    split. { destruct PVER as ([pad VC] & VR). split; [| exact VR]. eexists. eapply rw_cells_transport; [exact VC| exact MU| exact WM|]. cbn [cells_size csize Nat.add].
             apply (DJ (P + 264)%Z 24%nat); [lia|]. eapply Forall_impl; [| exact FW]. cbn. intros [l' h'] X0; cbn in *. lia. }
    split. { destruct PRS_ as [RC RR]. split; [| exact RR]. eapply rw_cells_transport; [exact RC| exact MU| exact WM|]. cbn [cells_size csize Nat.add].
             apply (DJ (P + 224)%Z 8%nat); [lia|]. eapply Forall_impl; [| exact FW]. cbn. intros [l' h'] X0; cbn in *. lia. }
    split. { eapply rw_cells_transport; [exact GM| exact MU| exact WM|]. cbn [cells_size csize Nat.add]. apply disjoint_from_Forall.
             eapply Forall_impl; [| exact FWlo]. cbn. intros [l' h'] X0; cbn in *. lia. }
    split. { eapply rw_cells_transport; [exact IW| exact MU| exact WM|]. cbn [cells_size csize Nat.add]. apply disjoint_from_Forall.
             eapply Forall_impl; [| exact FWlo]. cbn. intros [l' h'] X0; cbn in *. lia. }
    destruct TABST as (tlo & thi & THst & T1 & T2). destruct ZST as (zlo & zhi & ZHst & Z1 & Z2).
    destruct (lo_static_img rsegs AI LOK tlo thi THst) as (tw & Htw & TW1 & TW2). pose proof (lo_img_ceiling rsegs AI LOK tw Htw).
    destruct (lo_static_img rsegs AI LOK zlo zhi ZHst) as (zw & Hzw & ZW1 & ZW2). pose proof (lo_img_ceiling rsegs AI LOK zw Hzw).
    eapply PHS_munch; [exact MU| exact WM| | | exact PH0]; apply disjoint_from_Forall; eapply Forall_impl; try exact FWlo; cbn; intros [l' h'] X0; cbn in *; lia.
  Qed.

  Definition wcls (LBw : list BLK) (iv : ivl) : Prop :=
    ((lo <= fst iv /\ snd iv <= q) \/ (q + 20 <= fst iv /\ snd iv <= q + 40))%Z
    \/ ((P + 384 <= fst iv /\ snd iv <= P + 400) \/ (P + 440 <= fst iv /\ snd iv <= P + 480) \/ (P + 488 <= fst iv /\ snd iv <= P + 496))%Z
    \/ (fst iv = al_errno L_ /\ snd iv = al_errno L_ + 4)%Z
    \/ (exists b, In b LBw /\ blk_addr b <= fst iv /\ snd iv <= blk_addr b + blk_size b)%Z.

  Definition peFX0 (m : mem) : Prop :=
    rw_cells rsegs m q [C8 (wz STR_CHUNKMSG); C8 (wz STR_FILE)] /\ (exists j16, rw_cells rsegs m (q + 16) [CB 4 j16]).

  #[using="LOK ERRNOV ERRNC GMST IWST TABA ZEROA PHS_munch TABST ZST QLO LO0 CEIL QP PB"] Lemma seg_ok : forall s LB m m' W (LBw : list BLK) A len cap okm bs ns hs X meth,
    RHEAP rsegs AI s LB m -> RENV rsegs AI m B -> hpx AI WE LBK (q + 144) m0 m ->
    bsub AI (hl_blocks AI ns hs ++ okb AI okm A cap ++ LBK) LB -> NoDup (map blk_id (hl_blocks AI ns hs ++ okb AI okm A cap ++ LBK)) ->
    (forall b, In b LBw -> In b (hl_blocks AI ns hs ++ okb AI okm A cap)) ->
    munch W m m' -> wmono rsegs m m' -> Forall (wcls LBw) W ->
    rw_cells rsegs m (q + 40) (peFS ra s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e) -> peFX q m ->
    p_msg AI m LB P A len cap okm bs -> p_hlist AI m P ns hs X -> p_meth m P meth -> p_ver m P isreq maj min -> p_rs m P rm sc ->
    rw_cells rsegs m GMAXA [C8 (wz gmax)] -> rw_cells rsegs m INITWASCALLED [C1 (Z_to_bv 8 0)] -> PHS m ->
    RHEAP rsegs AI s LB m' /\ RENV rsegs AI m' B /\ hpx AI WE LBK (q + 144) m0 m'
    /\ rw_cells rsegs m' (q + 40) (peFS ra s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e)
    /\ (Forall (fun iv => snd iv <= q + 20 \/ q + 40 <= fst iv)%Z W -> peFX q m')
    /\ p_meth m' P meth /\ p_ver m' P isreq maj min /\ p_rs m' P rm sc
    /\ rw_cells rsegs m' GMAXA [C8 (wz gmax)] /\ rw_cells rsegs m' INITWASCALLED [C1 (Z_to_bv 8 0)]
    /\ ((forall b, In b LBw -> In b (hl_blocks AI ns hs)) -> p_msg AI m' LB P A len cap okm bs)
    /\ ((forall b, In b LBw -> In b (okb AI okm A cap)) -> p_hlist AI m' P ns hs X)
    /\ peFX0 m' /\ PHS m'.
  Proof.
    intros s LB m m' W LBw A len cap okm bs ns hs X meth HR HE HP BSUB ND SUBW MU WM FW FSH FX PMSG PHL PMETH PVER PRS_ GM IW PH0.
    pose proof alloc_ceiling_bounds as CE. pose proof alloc_ceiling_aligned8 as CE8.
    destruct (lo_errno_img rsegs AI LOK) as (we & Hwe & WE1 & WE2). pose proof (lo_img_ceiling rsegs AI LOK we Hwe) as WE3. rewrite ERRNOV in WE1, WE2.
    destruct (proj1 (bsub_app AI _ _ _) BSUB) as [SUBH BSUB2]. destruct (proj1 (bsub_app AI _ _ _) BSUB2) as [SUBM SUBK].
    assert (SUBHM : forall b, In b (hl_blocks AI ns hs ++ okb AI okm A cap) -> In b LB).
    { intros b Hb. apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [exact (SUBH b Hb)| exact (SUBM b Hb)]. }
    assert (SUBW' : forall b, In b LBw -> In b LB) by (intros b Hb; apply SUBHM; apply SUBW; exact Hb).

    assert (BWR : forall b, In b LBw -> (0 < blk_addr b /\ blk_addr b + blk_size b <= alloc_ceiling /\ (blk_addr b + blk_size b <= fst we \/ snd we <= blk_addr b))%Z).
    { intros b Hb. destruct (ai_block_range rsegs AI _ _ _ _ HR (SUBW' b Hb)) as (R1 & _ & _ & R4 & RF).
      pose proof (proj1 (List.Forall_forall _ _) RF we Hwe) as X0. cbn in X0. lia. }

    assert (DJW : forall X0 n, (forall iv, In iv W -> wcls LBw iv -> snd iv <= X0 \/ X0 + Z.of_nat n <= fst iv)%Z -> disjoint_from W X0 (Z.of_nat n)).
    { intros X0 n HX. apply disjoint_from_Forall. apply List.Forall_forall. intros iv Hiv. apply (HX iv Hiv). exact (proj1 (List.Forall_forall _ _) FW iv Hiv). }
    split. { eapply (ai_heap_frame rsegs AI); [exact HR| exact MU| exact WM|]. eapply Forall_impl; [| exact FW]. cbn. intros [l' h'] C; cbn in *.
             destruct C as [C|[C|[C|(b & Hb & C1 & C2)]]]; cbn in *; [left; lia| left; lia| right; right; left; lia| right; right; right].
             exists b. split; [exact (SUBW' b Hb)| cbn; lia]. }
    split. { eapply (ai_env_frame rsegs AI); [exact HR| exact HE| exact MU| exact WM|]. eapply Forall_impl; [| exact FW]. cbn. intros [l' h'] C; cbn in *.
             destruct C as [C|[C|[C|(b & Hb & C1 & C2)]]]; cbn in *; [left; lia| left; lia| right; right; left; lia| right; right; right].
             exists b. split; [exact (SUBW' b Hb)| cbn; lia]. }
    split. { eapply (hpx_trans rsegs AI); [exact HP|]. eapply (hpx_seg rsegs AI); [exact LOK| exact HR| exact SUBK| exact MU| exact WM|].
             eapply Forall_impl; [| exact FW]. cbn. intros [l' h'] C; cbn in *.
             destruct C as [C|[C|[C|(b & Hb & C1 & C2)]]]; cbn in *.
             - left. lia.
             - right; right. unfold WE, inside. cbn. lia.
             - right; left. intros a Ha [Hc|[(slo & shi & Hst & Hr)|(b0 & Hb0 & Hr0)]]; [lia| |].
               + pose proof (ERRNC slo shi Hst). rewrite ERRNOV in *. lia.
               + destruct (ai_block_range rsegs AI _ _ _ _ HR (SUBK b0 Hb0)) as (_ & _ & _ & _ & RF).
                 pose proof (proj1 (List.Forall_forall _ _) RF we Hwe) as X0. cbn in X0. lia.
             - right; left. intros a Ha. eapply (fresh_block_not_client rsegs AI); [exact LOK| exact HR| exact (SUBW' b Hb)| | lia| lia].
               intros b0 Hb0. split; [exact (SUBK b0 Hb0)|]. intros ->.
               pose proof ND as ND'. rewrite (app_assoc (hl_blocks AI ns hs)) in ND' || rewrite <- (app_assoc (hl_blocks AI ns hs)) in ND'.
               exact (nodup_in_neq AI _ _ _ _ ND' (SUBW b Hb) Hb0 eq_refl). }

    assert (UP : forall X0 n, (q <= X0)%Z -> (X0 + Z.of_nat n <= P + 384 \/ (P + 400 <= X0 /\ X0 + Z.of_nat n <= P + 432) \/ (P + 480 <= X0 /\ X0 + Z.of_nat n <= P + 488) \/ P + 496 <= X0)%Z ->
                 (X0 + Z.of_nat n <= P + 504)%Z -> (X0 + Z.of_nat n <= q + 20 \/ q + 40 <= X0)%Z -> disjoint_from W X0 (Z.of_nat n)).
    { intros X0 n H1 H2 H3 H4. apply DJW. intros [l' h'] _ C. unfold wcls in C. cbn in *. destruct C as [C|[C|[C|(b & Hb & C1 & C2)]]]; [lia| lia| lia|].
      destruct (BWR b Hb) as (R1 & R4 & _). lia. }

    assert (UPS : Forall (fun iv => snd iv <= q + 20 \/ q + 40 <= fst iv)%Z W -> disjoint_from W (q + 20) 20).
    { intros FW5. apply disjoint_from_Forall. eapply Forall_impl; [| exact FW5]. cbn. intros [l' h'] C5; cbn in *. lia. }

    assert (LOWS : forall X0 n, (X0 + Z.of_nat n <= lo)%Z -> (X0 + Z.of_nat n <= al_errno L_ \/ al_errno L_ + 4 <= X0)%Z ->
                 (exists slo shi, al_client_static L_ slo shi /\ slo <= X0 /\ X0 + Z.of_nat n <= shi)%Z -> disjoint_from W X0 (Z.of_nat n)).
    { intros X0 n H1 H2 (slo & shi & Hst & H3 & H4). destruct (lo_static_img rsegs AI LOK slo shi Hst) as (w & Hw & W1' & W2').
      apply DJW. intros [l' h'] _ C. unfold wcls in C. cbn in *. destruct C as [C|[C|[C|(b & Hb & C1 & C2)]]]; [lia| lia| lia|].
      destruct (ai_block_range rsegs AI _ _ _ _ HR (SUBW' b Hb)) as (_ & _ & _ & _ & RF).
      pose proof (proj1 (List.Forall_forall _ _) RF w Hw) as X1. cbn in X1. lia. }
    split. { eapply rw_cells_transport; [exact FSH| exact MU| exact WM|]. unfold peFS. cbn [cells_size csize Nat.add]. apply UP; lia. }
    assert (D20 : disjoint_from W q 20) by (apply (UP q 20%nat); lia).
    split. { intros FW5. pose proof (UPS FW5) as D40. destruct FX as (Q0 & [j16 Q16] & [cz Q20] & (da & db & Q24)).
             split. { eapply rw_cells_transport; [exact Q0| exact MU| exact WM|]. eapply disjoint_from_sub; [exact D20| lia| cbn; lia]. }
             split. { eexists. eapply rw_cells_transport; [exact Q16| exact MU| exact WM|]. eapply disjoint_from_sub; [exact D20| lia| cbn; lia]. }
             split. { eexists. eapply rw_cells_transport; [exact Q20| exact MU| exact WM|]. eapply disjoint_from_sub; [exact D40| lia| cbn; lia]. }
             do 2 eexists. eapply rw_cells_transport; [exact Q24| exact MU| exact WM|]. eapply disjoint_from_sub; [exact D40| lia| cbn; lia]. }
    split. { destruct PMETH as [MC MR]. split; [| exact MR]. eapply rw_cells_transport; [exact MC| exact MU| exact WM|]. cbn [cells_size csize Nat.add]. apply UP; lia. }
    split. { destruct PVER as ([pad VC] & VR). split; [| exact VR]. eexists. eapply rw_cells_transport; [exact VC| exact MU| exact WM|]. cbn [cells_size csize Nat.add]. apply UP; lia. }
    split. { destruct PRS_ as [RC RR]. split; [| exact RR]. eapply rw_cells_transport; [exact RC| exact MU| exact WM|]. cbn [cells_size csize Nat.add]. apply UP; lia. }
    split. { eapply rw_cells_transport; [exact GM| exact MU| exact WM|]. cbn [cells_size csize Nat.add]. apply (LOWS GMAXA 8%nat); [lia| rewrite ERRNOV; lia|].
             destruct GMST as (slo & shi & Hst & G1 & G2). exists slo, shi. split; [exact Hst| cbn; lia]. }
    split. { eapply rw_cells_transport; [exact IW| exact MU| exact WM|]. cbn [cells_size csize Nat.add]. apply (LOWS INITWASCALLED 1%nat); [lia| rewrite ERRNOV; lia|].
             destruct IWST as (slo & shi & Hst & G1 & G2). exists slo, shi. split; [exact Hst| cbn; lia]. }

    assert (HPgen : forall LBh : list BLK, (forall b, In b LBh -> In b LB) -> (forall b b', In b LBh -> In b' LBw -> b <> b') -> heap_pres AI LBh HI64 m m').
    { intros LBh S1 S2 a Ha Hc. split; [| intros Hw; apply WM; exact Hw].
      unfold munch in MU. pose proof (MU (wa a)) as E. unfold wa in E. rewrite unsigned_lit in E by lia. apply E.
      apply outside_of_forall. eapply Forall_impl; [| exact FW]. cbn. intros [l' h'] C; cbn in *.
      destruct Hc as [Hc|[(slo & shi & Hst & Hr)|(b0 & Hb0 & Hr0)]]; [unfold HI64 in Hc; lia| |].
      - destruct (lo_static_img rsegs AI LOK slo shi Hst) as (w & Hw & W1' & W2'). pose proof (lo_img_ceiling rsegs AI LOK w Hw).
        pose proof (ERRNC slo shi Hst).
        destruct C as [C|[C|[C|(b & Hb & C1 & C2)]]]; cbn in *; [lia| lia| lia|].
        destruct (ai_block_range rsegs AI _ _ _ _ HR (SUBW' b Hb)) as (_ & _ & _ & _ & RF).
        pose proof (proj1 (List.Forall_forall _ _) RF w Hw) as X0. cbn in X0. lia.
      - destruct (ai_block_range rsegs AI _ _ _ _ HR (S1 b0 Hb0)) as (_ & _ & _ & R4 & RF).
        destruct C as [C|[C|[C|(b & Hb & C1 & C2)]]]; cbn in *; [lia| lia| |].
        + pose proof (proj1 (List.Forall_forall _ _) RF we Hwe) as X0. cbn in X0. lia.
        + pose proof (ai_blocks_disjoint rsegs AI _ _ _ _ _ HR (S1 b0 Hb0) (SUBW' b Hb) (S2 b0 b Hb0 Hb)). lia. }
    split.
    { intros LBWH. eapply pe_msg_pres; [exact PMSG| exact MU| exact WM| apply (UP (P + 400)%Z 32%nat); lia| | intros b Hb; exact Hb| exact SUBM].
      apply HPgen; [exact SUBM|]. intros b b' Hb Hb' ->. exact (nodup_in_neq AI _ _ _ _ ND (LBWH b' Hb') (in_or_app _ _ _ (or_introl Hb)) eq_refl). }
    split.
    { intros LBWM. eapply pe_hlist_pres; [exact PHL| exact MU| exact WM| apply (UP (P + 288)%Z 96%nat); lia| | intros b Hb; exact Hb].
      apply HPgen; [exact SUBH|]. intros b b' Hb Hb' E.
      refine (nodup_in_neq AI _ _ _ _ ND Hb (in_or_app _ _ _ (or_introl (LBWM b' Hb'))) E). }
    destruct FX as (Q0 & [j16 Q16] & _).
    split. { split. { eapply rw_cells_transport; [exact Q0| exact MU| exact WM|]. eapply disjoint_from_sub; [exact D20| lia| cbn; lia]. }
             eexists. eapply rw_cells_transport; [exact Q16| exact MU| exact WM|]. eapply disjoint_from_sub; [exact D20| lia| cbn; lia]. }

    destruct TABST as (tlo & thi & THst & T1 & T2). destruct ZST as (zlo & zhi & ZHst & Z1 & Z2).
    destruct (lo_static_img rsegs AI LOK tlo thi THst) as (tw & Htw & TW1 & TW2). pose proof (lo_img_ceiling rsegs AI LOK tw Htw).
    destruct (lo_static_img rsegs AI LOK zlo zhi ZHst) as (zw & Hzw & ZW1 & ZW2). pose proof (lo_img_ceiling rsegs AI LOK zw Hzw).
    pose proof (ERRNC tlo thi THst). pose proof (ERRNC zlo zhi ZHst).
    eapply PHS_munch; [exact MU| exact WM| | | exact PH0].
    - apply (LOWS TABA 528%nat); [cbn; lia| cbn; lia| exists tlo, thi; split; [exact THst| cbn; lia]].
    - apply (LOWS ZEROA 1%nat); [cbn; lia| cbn; lia| exists zlo, zhi; split; [exact ZHst| cbn; lia]].
  Qed.

  #[using="TPV QLO"] Lemma pe_case_default : forall s LB m cur A len cap okm bs ebw elw err hack pos entp clen csz esp ns hs X meth
      gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 t3 t4 t5 t6 x1 (F : bvmap 5 word) fc,
    PI s LB m cur A len cap okm bs ebw elw err hack pos entp clen csz esp ns hs X meth ->
    SREACH AI (pent_post gp F fc) (PRS 0x159c4 x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (wz S) s7 t3 t4 t5 t6 gp F fc m) s LB.
  Proof.
    intros until fc. intros INV.
    eapply sreach_evt. { rewrite TPV. apply (pe_default P q). }
    intros ms' ->. rewrite <- TPV. eapply pe_exit; [exact INV| lia| lia].
  Qed.

  #[using="LOK TPV ERRNOV BLK4096 BLKIMG TABA ZEROA PHS_munch TABST ZST QLO LO0 CEIL QP PB BHI GMX"] Lemma pe_case4 : forall s LB m cur A len cap okm bs ebw elw err hack pos entp clen csz esp ns hs X meth
      gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 t3 t4 t5 t6 x1 (F : bvmap 5 word) fc,
    PI s LB m cur A len cap okm bs ebw elw err hack pos entp clen csz esp ns hs X meth -> entp = 4 -> (0 < A)%Z ->
    SREACH AI (pent_post gp F fc) (PRS 0x158fc x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (wz S) s7 t3 t4 t5 t6 gp F fc m) s LB.
  Proof.
    intros until fc. intros INV E4 APOS. pose proof INV as INV0. open_PI INV. subst entp.
    destruct (msg_facts _ _ _ _ _ _ _ _ HR PMSG) as (HL & HC & A0 & AHI & OKS & OKN). unfold LMAX in HC.
    destruct PVER as ([pad VERC] & ISR & MJR & MNR). destruct PCTL as (CTL & CTLB). unfold p_ctl_cells in CTL.
    destruct EOK as (ESP & _ & _). specialize (ESP ltac:(lia)).
    unfold p_scan in PSC. unfold p_ent in PENT. destruct PMSG as (MBC & OWN & HL' & HC' & NULM).
    eapply sreach_evt.
    { rewrite TPV. eapply (pe_until P q PHI63 A len cap cur esp isreq maj min err hack pos 4 clen csz); unfold ctl9; try eassumption; try LiaTuning.alia. }
    intros ms' (m1 & a1' & a2' & a3' & a4' & -> & MU1 & WM1 & MI1 & MBC1 & SC1 & VERC1 & ENT1 & CTL1). rewrite <- TPV.
    destruct (PI_seg s LB m m1 _ A len cap okm bs ns hs X meth HR HE HPX BSUB MU1 WM1 ltac:(fw)
                FSH FX (conj MBC (conj OWN (conj HL' (conj HC' NULM)))) PHL PMETH (conj (ex_intro _ pad VERC) (conj ISR (conj MJR MNR))) PRS_ GM IW PH)
      as (HR1 & HE1 & HP1 & FSH1 & FX1 & PMSG1 & PHL1 & PMETH1 & PVER1 & PRS1 & GM1 & IW1 & PH1).
    pose proof (rw_cells_transport rsegs _ m m1 _ _ ERR MU1 WM1 ltac:(rewrite ERRNOV; cbn; lia)) as ERR1.
    assert (ST1 : stk rsegs m1 lo q). { eapply (stk_transport_disjoint rsegs); [| exact MU1| exact WM1| cbn; lia]. exact ST. }
    eapply (pe_exit s LB m1 len A len cap okm bs (wz (A + esp)) (wz (len - esp)) err hack pos 4 clen csz esp ns hs X meth 2); [| lia| lia].
    split; [exact HR1|]. split; [exact HE1|]. split; [exact MI1|]. split; [exact ST1|]. split; [eexists; exact ERR1|].
    split; [exact FSH1|]. split; [exact FX1|]. split; [exact SC1|]. split; [exact PMSG1|]. split; [lia|].
    split; [exact ENT1|]. split; [split; [exact CTL1| exact CTLB]|]. split; [exact PHL1|]. split; [lia|].
    split; [exact PMETH1|]. split; [exact PVER1|]. split; [exact PRS1|]. split; [exact BSUB|]. split; [exact ND|].
    split; [exact GM1|]. split; [exact IW1|]. split; [exact HP1|]. split; [exact PH1|].
    unfold ent_ok in *. repeat split; intros; lia.
  Qed.

  Definition CONT (M : Z) (gp : word) (F : bvmap 5 word) (fc : bv 32) : Prop :=
    forall s LB m cur A len cap km bs ebw elw err hack pos entp clen csz esp ns hs X meth t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 t3 t4 t5 t6 x1,
      PI s LB m cur A len cap (Some km) bs ebw elw err hack pos entp clen csz esp ns hs X meth -> (pe_meas entp elw < M)%Z ->
      SREACH AI (pent_post gp F fc) (PRS 0x157b0 x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (wz S) s7 t3 t4 t5 t6 gp F fc m) s LB.

  #[using="TPV QLO"] Lemma pe_cont : forall M gp F fc s LB m cur A len cap km bs ebw elw err hack pos entp clen csz esp ns hs X meth (r : Z)
      t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s7 t3 t4 t5 t6 x1,
    CONT M gp F fc -> PI s LB m cur A len cap (Some km) bs ebw elw err hack pos entp clen csz esp ns hs X meth ->
    (0 <= r <= 6)%Z -> r <> 4 -> (r = 6 -> pe_meas entp elw < M)%Z ->
    SREACH AI (pent_post gp F fc) (PRS 0x157ac x1 t0 t1 t2 (wz r) a1 a2 a3 a4 a5 a6 a7 (wz S) s7 t3 t4 t5 t6 gp F fc m) s LB.
  Proof.
    intros until x1. intros HC INV RR R4 RM.
    eapply sreach_evt. { rewrite TPV. apply (pe_head P q r); lia. }
    intros ms' [[NR ->]|[-> ->]]; rewrite <- TPV.
    - eapply pe_exit; [exact INV| lia| exact R4].
    - eapply HC; [exact INV| apply RM; reflexivity].
  Qed.

  Definition bV (h : hdr) : BLK := (vk AI h, vA AI h, vcap AI h + 1)%Z.
  #[using="Type"] Lemma bV_in : forall ns hs h, In h hs -> In (bV h) (hl_blocks AI ns hs).
  Proof.
    intros ns hs h H. unfold hl_blocks. apply in_or_app. right. unfold hdrs_blocks. apply in_concat. exists (hblocks AI h).
    split; [apply in_map; exact H| cbn; right; left; reflexivity].
  Qed.

  #[using="LOK TPV ERRNOV CAN ERRNC BLK4096 BLKIMG GERM GMST IWST TABA ZEROA PHS_munch TABST ZST QLO LO0 CEIL QP PB BHI GMX P8 Q8"] Lemma pe_case1 : forall M gp F fc s LB m cur A len cap km bs ebw elw err hack pos entp clen csz esp ns hs X meth
      t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 t3 t4 t5 t6 x1,
    CONT M gp F fc -> PI s LB m cur A len cap (Some km) bs ebw elw err hack pos entp clen csz esp ns hs X meth -> entp = 1 -> M = pe_meas entp elw ->
    SREACH AI (pent_post gp F fc) (PRS 0x157a4 x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (wz S) s7 t3 t4 t5 t6 gp F fc m) s LB.
  Proof.
    intros until x1. intros HC INV E1 HM. pose proof INV as INV0. open_PI INV. subst entp.
    pose proof P8 as P8z. pose proof Q8 as Q8z. unfold pmod8 in P8z, Q8z.
    destruct (msg_facts _ _ _ _ _ _ _ _ HR PMSG) as (HL & HC' & A0 & AHI & OKS & OKN). unfold LMAX in HC'.
    destruct (CAN _ _ _ HR) as [SSP1 [canary SSP2]].
    destruct (proj1 (bsub_app AI _ _ _) BSUB) as [SUBH BSUB2].
    assert (NDH : NoDup (map blk_id (hl_blocks AI ns hs))).
    { rewrite map_app in ND. apply list.NoDup_app in ND. destruct ND as (NDH & _). exact NDH. }
    assert (EQq : bv_unsigned (wz q) = q) by (apply unsigned_lit; lia).
    assert (EQt : bv_unsigned (wz (al_tp L_)) = al_tp L_) by (rewrite TPV; apply unsigned_lit; lia).
    eapply sreach_evt. { rewrite TPV. apply (pe_germ P q). }
    intros ms1 ->. rewrite <- TPV.
    pose proof GERM as G. unfold germ_stmt in G.
    eapply sreach_evt.
    { eapply G; rewrite ?EQq, ?EQt, ?TPV, ?ERRNOV in *; unfold got_ssp, ssp_guard, GERM_DEPTH; try eassumption; try reflexivity; try lia. }
    clear G. intros ms2 PO. unfold germ_post in PO.
    destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & r & err' & hack' & pos' & entp' & clen' & errv'
                    & -> & MU2 & WM2 & MI2 & ST2 & PENT2 & PCTL2 & PHL2 & ERR2 & SSP1' & SSP2' & IW2 & RES).
    rewrite ?EQq, ?EQt in MU2. rewrite ?EQq in ST2. rewrite ?EQt, TPV in ERR2.
    replace (ret_pc (wz 0x157ac)) with (wz 0x157ac : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).

    assert (FW : Forall (wcls (map bV hs)) (germ_W AI lo q P (al_tp L_ - 164) hs)).
    { unfold germ_W. rewrite TPV. repeat apply Forall_cons.
      1-4: unfold wcls; rewrite ?ERRNOV; cbn; lia.
      apply List.Forall_forall. intros iv Hiv. apply in_map_iff in Hiv. destruct Hiv as (h & <- & Hh). unfold wcls. right; right; right.
      exists (bV h). split; [apply in_map; exact Hh| cbn; lia]. }
    destruct (seg_ok s LB m m2 _ (map bV hs) A len cap (Some km) bs ns hs X meth HR HE HPX BSUB ND
                ltac:(intros b Hb; apply in_map_iff in Hb; destruct Hb as (h & <- & Hh); apply in_or_app; left; apply bV_in; exact Hh)
                MU2 WM2 FW FSH FX PMSG PHL PMETH PVER PRS_ GM IW PH)
      as (HR2 & HE2 & HP2 & FSH2 & FX2 & PMETH2 & PVER2 & PRS2 & GM2 & IW2' & PMSG2 & _ & _ & PH2).
    specialize (PMSG2 ltac:(intros b Hb; apply in_map_iff in Hb; destruct Hb as (h & <- & Hh); apply bV_in; exact Hh)).
    specialize (FX2 ltac:(unfold germ_W; rewrite TPV; repeat apply Forall_cons; [cbn; lia| cbn; lia| cbn; lia| cbn; lia|];
                           apply List.Forall_forall; intros iv Hiv; apply in_map_iff in Hiv; destruct Hiv as (h & <- & Hh); cbn;
                           destruct (ai_block_range rsegs AI _ _ _ _ HR (SUBH _ (bV_in ns hs h Hh))) as (_ & _ & _ & R4 & _); cbn in R4; lia)).
    assert (RF : (0 <= r <= 6)%Z /\ (r = 6 -> pos' = pos /\ 2 <= entp' <= 4 /\ err' = err)%Z /\ (r <> 6 -> entp' = 1 \/ 2 <= entp' <= 4)%Z).
    { destruct RES as [(-> & -> & -> & -> & ->)|[(-> & -> & E3 & -> & ->)|(-> & -> & -> & ->)]]; (repeat split); intros; lia. }
    destruct RF as (RR & R6 & RN6).
    destruct PCTL2 as (CTL2 & CB2).

    assert (INV2 : PI s LB m2 cur A len cap (Some km) bs (wz (A + cur)) (wz 0) err' hack' pos' entp' clen' csz cur ns hs X meth).
    { split; [exact HR2|]. split; [exact HE2|]. split; [exact MI2|]. split; [exact ST2|]. split; [eexists; rewrite ERRNOV; exact ERR2|].
      split; [exact FSH2|]. split; [exact FX2|]. split.
      { unfold p_scan in PSC |- *. eapply rw_cells_transport; [exact PSC| exact MU2| exact WM2|]. cbn [cells_size csize Nat.add].
        apply disjoint_from_Forall. unfold germ_W. repeat apply Forall_cons. 1-4: cbn; rewrite ?TPV; lia.
        apply List.Forall_forall. intros iv Hiv. apply in_map_iff in Hiv. destruct Hiv as (h & <- & Hh). cbn.
        destruct (proj1 (bsub_app AI _ _ _) BSUB) as [SUBH' _].
        destruct (ai_block_range rsegs AI _ _ _ _ HR (SUBH' _ (bV_in ns hs h Hh))) as (_ & _ & _ & R4 & _). cbn in R4. lia. }
      split; [exact PMSG2|]. split; [lia|]. split; [exact PENT2|]. split; [split; [exact CTL2| exact CB2]|]. split; [exact PHL2|]. split; [exact XV|].
      split; [exact PMETH2|]. split; [exact PVER2|]. split; [exact PRS2|]. split; [exact BSUB|]. split; [exact ND|].
      split; [exact GM2|]. split; [exact IW2|]. split; [exact HP2|]. split; [exact PH2|].
      unfold ent_ok. split; [intros; lia|]. split; [| intros E5; exfalso].
      - intros _. exists 0. split; [reflexivity| lia].
      - destruct (Z.eq_dec r 6) as [E|NE]; [destruct (R6 E) as (_ & B6 & _); lia| destruct (RN6 NE); lia]. }
    eapply (pe_cont M gp F fc); [exact HC| exact INV2| lia| destruct RES as [(-> & _)|[(-> & _)|(-> & _)]]; lia|].
    intros E6. destruct (R6 E6) as (_ & B6 & _). rewrite HM. unfold pe_meas, elen_of.
    rewrite unsigned_lit by lia. cbn [Z.eqb Pos.eqb].
    destruct (Z.eqb_spec entp' 1); [lia|]. destruct (Z.eqb_spec entp' 3); [lia|]. destruct (Z.eqb_spec entp' 5); lia.
  Qed.

  #[using="LOK TPV ERRNOV ERRNC BLK4096 BLKIMG GMST IWST TABA ZEROA PHS_munch TABST ZST QLO LO0 CEIL QP PB BHI GMX"] Lemma pe_case2 : forall s LB m cur A len cap okm bs ebw elw err hack pos entp clen csz esp ns hs X meth
      gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 t3 t4 t5 t6 x1 (F : bvmap 5 word) fc,
    PI s LB m cur A len cap okm bs ebw elw err hack pos entp clen csz esp ns hs X meth -> entp = 2 -> (0 < A)%Z ->
    SREACH AI (pent_post gp F fc) (PRS 0x15940 x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (wz S) s7 t3 t4 t5 t6 gp F fc m) s LB.
  Proof.
    intros until fc. intros INV E2 APOS. pose proof INV as INV0. open_PI INV. subst entp.
    pose proof alloc_ceiling_bounds as CE. pose proof alloc_ceiling_aligned8 as CE8.
    destruct (msg_facts _ _ _ _ _ _ _ _ HR PMSG) as (HL & HC & A0 & AHI & OKS & OKN). unfold LMAX in HC.
    pose proof PVER as PVER0. pose proof PMSG as PMSG0.
    destruct PVER as ([pad VERC] & ISR & MJR & MNR). destruct PCTL as (CTL & CTLB). unfold p_ctl_cells in CTL.
    pose proof EOK as EOK0. destruct EOK as (ESP & _ & _). specialize (ESP ltac:(lia)).
    unfold p_scan in PSC. unfold p_ent in PENT. destruct PMSG as (MBC & OWN & HL' & HC' & NULM).

    assert (BLKC : (clen < len - esp)%Z -> (0 < A)%Z /\ (A + (cap + 1) <= lo)%Z /\ rw_cells rsegs m A [CB (Z.to_nat (cap + 1)) bs]).
    { intros LT. destruct okm as [km|]; [| destruct (OKN eq_refl) as (_ & L0 & _); exfalso; lia].
      destruct (OKS km eq_refl) as (HIN & BLK & A4 & _). split; [lia|]. split; [lia| exact BLK]. }
    eapply sreach_evt.
    { rewrite TPV. eapply (pe_clen P q lo QLO1 QP PHI63 A len cap cur esp isreq maj min err hack pos 2 clen csz ebw); unfold ctl9; try eassumption; try LiaTuning.alia. }
    intros ms' (m1 & r & pos' & el' & eb' & bs' & a0' & a1' & a2' & a3' & -> & -> & CASES & WM1 & MI1 & MBC1 & VERC1 & ENT1 & CTL1 & LBS' & NTH' & RES). rewrite <- TPV.
    assert (RB : (0 <= r <= 1)%Z /\ (0 <= pos' <= 4)%Z) by (destruct RES as [(-> & -> & _)|(-> & -> & _)]; lia).
    rename PMSG0 into PMSG. rename PVER0 into PVER.
    destruct CASES as [(-> & MU1)|(LT & -> & MU1 & BLK1)].
    -
      destruct (PI_seg s LB m m1 _ A len cap okm bs ns hs X meth HR HE HPX BSUB MU1 WM1 ltac:(fw) FSH FX PMSG PHL PMETH PVER PRS_ GM IW PH)
        as (HR1 & HE1 & HP1 & FSH1 & FX1 & PMSG1 & PHL1 & PMETH1 & PVER1 & PRS1 & GM1 & IW1 & PH1).
      pose proof (rw_cells_transport rsegs _ m m1 _ _ ERR MU1 WM1 ltac:(rewrite ERRNOV; cbn; lia)) as ERR1.
      pose proof (rw_cells_transport rsegs _ m m1 _ _ PSC MU1 WM1 ltac:(cbn; lia)) as SC1.
      assert (ST1 : stk rsegs m1 lo q). { eapply (stk_transport_disjoint rsegs); [| exact MU1| exact WM1| cbn; lia]. exact ST. }
      eapply (pe_exit s LB m1 cur A len cap okm bs eb' (wz el') err hack pos' 2 clen csz esp ns hs X meth r); [| lia| lia].
      split; [exact HR1|]. split; [exact HE1|]. split; [exact MI1|]. split; [exact ST1|]. split; [eexists; exact ERR1|].
      split; [exact FSH1|]. split; [exact FX1|]. split; [exact SC1|]. split; [exact PMSG1|]. split; [lia|].
      split; [exact ENT1|]. split; [split; [exact CTL1| lia]|]. split; [exact PHL1|]. split; [exact XV|].
      split; [exact PMETH1|]. split; [exact PVER1|]. split; [exact PRS1|]. split; [exact BSUB|]. split; [exact ND|].
      split; [exact GM1|]. split; [exact IW1|]. split; [exact HP1|]. split; [exact PH1|].
      unfold ent_ok in *. repeat split; intros; lia.
    -
      destruct okm as [km|]; [| destruct (OKN eq_refl) as (_ & L0 & _); exfalso; lia].
      destruct (OKS km eq_refl) as (HIN & BLK0 & A4 & AW).
      set (bm := (km, A, cap + 1)%Z : BLK).
      assert (INB : forall b, In b [bm] -> In b (okb AI (Some km) A cap)) by (intros b [<-|[]]; left; reflexivity).
      assert (FW : Forall (wcls [bm]) [(P + 384, P + 400); (P + 448, P + 452); (A + (esp + clen), A + (esp + clen) + 1)]%Z).
      { repeat apply Forall_cons; try apply Forall_nil; unfold wcls; cbn; [lia| lia|]. right; right; right. exists bm. split; [left; reflexivity| cbn; lia]. }
      destruct (seg_ok s LB m m1 _ [bm] A len cap (Some km) bs ns hs X meth HR HE HPX BSUB ND
                  ltac:(intros b Hb; apply in_or_app; right; exact (INB b Hb)) MU1 WM1 FW FSH FX PMSG PHL PMETH PVER PRS_ GM IW PH)
        as (HR1 & HE1 & HP1 & FSH1 & FX1 & PMETH1 & PVER1 & PRS1 & GM1 & IW1 & _ & PHL1 & _ & PH1).
      specialize (PHL1 INB). specialize (FX1 ltac:(repeat apply Forall_cons; try apply Forall_nil; cbn; lia)).
      pose proof (rw_cells_transport rsegs _ m m1 _ _ ERR MU1 WM1 ltac:(rewrite ERRNOV; cbn; lia)) as ERR1.
      pose proof (rw_cells_transport rsegs _ m m1 _ _ PSC MU1 WM1 ltac:(cbn; lia)) as SC1.
      assert (ST1 : stk rsegs m1 lo q). { eapply (stk_transport_disjoint rsegs); [| exact MU1| exact WM1| cbn; lia]. exact ST. }
      assert (PMSG1 : p_msg AI m1 LB P A len cap (Some km) (set_byte bs (Z.to_nat (esp + clen)) (Z_to_bv 8 0))).
      { split; [exact MBC1|]. split; [cbn; split; [exact HIN| exact BLK1]|]. split; [lia|]. split; [exact HC'|]. cbn. cbn in NULM. rewrite NTH'. exact NULM. }
      eapply (pe_exit s LB m1 cur A len cap (Some km) _ eb' (wz el') err hack pos' 2 clen csz esp ns hs X meth r); [| lia| lia].
      split; [exact HR1|]. split; [exact HE1|]. split; [exact MI1|]. split; [exact ST1|]. split; [eexists; exact ERR1|].
      split; [exact FSH1|]. split; [exact FX1|]. split; [exact SC1|]. split; [exact PMSG1|]. split; [lia|].
      split; [exact ENT1|]. split; [split; [exact CTL1| lia]|]. split; [exact PHL1|]. split; [exact XV|].
      split; [exact PMETH1|]. split; [exact PVER1|]. split; [exact PRS1|]. split; [exact BSUB|]. split; [exact ND|].
      split; [exact GM1|]. split; [exact IW1|]. split; [exact HP1|]. split; [exact PH1|].
      unfold ent_ok in *. repeat split; intros; lia.
  Qed.

  #[using="Type"] Lemma nodup_ids_neq : forall (OB1 OB2 : list BLK) b1 b2,
    NoDup (map blk_id (OB1 ++ OB2)) -> In b1 OB1 -> In b2 OB2 -> blk_id b1 <> blk_id b2.
  Proof.
    intros OB1 OB2 b1 b2 ND0 H1 H2 E. rewrite map_app in ND0. apply list.NoDup_app in ND0. destruct ND0 as (_ & DJ & _).
    apply (DJ (blk_id b1)); apply base.list_elem_of_In; [apply in_map; exact H1| rewrite E; apply in_map; exact H2].
  Qed.

  #[using="LOK CEIL"] Lemma hpx_heap_pres_low : forall s (LB0 LBq : list BLK) m1 Wd SPq (LBh : list BLK) m m',
    RHEAP rsegs AI s LB0 m1 -> (forall b, In b LBh -> In b LBq) -> (forall b, In b LBq -> In b LB0) -> hpx AI Wd LBq SPq m m' ->
    Forall (fun iv => lo <= fst iv)%Z Wd -> heap_pres AI LBh HI64 m m'.
  Proof.
    intros s LB0 LBq m1 Wd SPq LBh m m' HR SUB SUB0 HP FW a Ha Hc.
    pose proof alloc_ceiling_bounds as CE. pose proof alloc_ceiling_aligned8 as CE8.
    assert (LOW : (a < lo)%Z /\ client_addr AI LBq SPq a).
    { destruct Hc as [Hc|[(slo & shi & Hst & Hr)|(b & Hb & Hr)]].
      - unfold HI64 in Hc. lia.
      - destruct (lo_static_img rsegs AI LOK slo shi Hst) as (w & Hw & W1 & W2). pose proof (lo_img_ceiling rsegs AI LOK w Hw).
        split; [lia|]. right; left. exists slo, shi. split; [exact Hst| exact Hr].
      - destruct (ai_block_range rsegs AI _ _ _ _ HR (SUB0 _ (SUB b Hb))) as (_ & _ & _ & R4 & _).
        split; [lia|]. right; right. exists b. split; [exact (SUB b Hb)| exact Hr]. }
    destruct LOW as [LOW CA]. apply (HP a Ha CA). apply outside_of_forall. eapply Forall_impl; [| exact FW]. cbn. intros [l h] Hl; cbn in *. lia.
  Qed.

  #[using="Type"] Lemma nth_error_firstn_snoc : forall (l l1 : list byte) (x : byte) n,
    firstn (Datatypes.S n) l = l1 ++ [x] -> length l1 = n -> nth_error l n = Some x.
  Proof.
    intros l l1 x n E L. rewrite <- (firstn_skipn (Datatypes.S n) l). rewrite E. rewrite nth_error_app1 by (rewrite app_length; cbn; lia).
    rewrite nth_error_app2 by lia. rewrite L, Nat.sub_diag. reflexivity.
  Qed.

  #[using="AC LOK REALLOCPC BLK4096 BLKIMG GMST IWST PHS_hp QLO QLO2 STK0 LO0 CEIL QP PB BHI GMX P8 Q8"] Lemma pe_mdel : forall gp (F : bvmap 5 word) fc s LB m A len cap km bs ebw elw err hack pos entp clen csz esp ns hs X meth scur xb (idx num rpc : Z)
      t0 t1 t2 a3 a4 a5 a6 a7 s2v s7 t3 t4 t5 t6,
    PC s LB m A len cap (Some km) bs ebw elw err hack pos entp clen csz esp ns hs X meth scur xb ->
    (0 <= idx)%Z -> (0 <= num)%Z -> (idx + num <= len)%Z -> ret_pc (wz rpc) = wz rpc ->
    (forall s' LB' m' A' len' cap' km' bs' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
        PC s' LB' m' A' len' cap' (Some km') bs' ebw elw err hack pos entp clen csz esp ns hs X meth scur (Z.min xb len') ->
        (len' = len - num \/ len' = len)%Z ->
        SREACH AI (pent_post gp F fc) (PRS rpc (wz rpc) t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s2v s7 t3' t4' t5' t6' gp F fc m') s' LB') ->
    SREACH AI (pent_post gp F fc) (PRS membuffer_delete_entry (wz rpc) t0 t1 t2 (wz MB) (wz idx) (wz num) a3 a4 a5 a6 a7 s2v s7 t3 t4 t5 t6 gp F fc m) s LB.
  Proof.
    intros until t6. intros INV I0 N0 INL RPC HK. open_PC INV.
    pose proof P8 as P8z. pose proof Q8 as Q8z. unfold pmod8 in P8z, Q8z.
    pose proof alloc_ceiling_bounds as CE. pose proof alloc_ceiling_aligned8 as CE8.
    assert (EQq : bv_unsigned (wz q) = q) by (apply unsigned_lit; lia).
    destruct (msg_facts _ _ _ _ _ _ _ _ HR PMSG) as (HL & HC & A0 & AHI & OKS & _). unfold LMAX in HC.
    destruct (OKS km eq_refl) as (HIN & BLKM & A4 & AW).
    destruct PMSG as (MBC & OWN & HL' & HC' & NULM).
    destruct (proj1 (bsub_app AI _ _ _) BSUB) as [SUBH BSUB2]. destruct (proj1 (bsub_app AI _ _ _) BSUB2) as [SUBM SUBK].
    set (bm := (km, A, cap + 1)%Z : BLK) in *.
    assert (INbm : In bm (okb AI (Some km) A cap)) by (left; reflexivity).

    assert (KSUBH : forall b, In b (hl_blocks AI ns hs) -> In b (lb_keep AI (Some km) LB)).
    { intros b Hb. cbn. apply (in_lb_remove AI); [exact (SUBH b Hb)|].
      exact (nodup_ids_neq _ _ b bm ND Hb (in_or_app _ _ _ (or_introl INbm))). }
    assert (KSUBK : forall b, In b LBK -> In b (lb_keep AI (Some km) LB)).
    { intros b Hb. cbn. apply (in_lb_remove AI); [exact (SUBK b Hb)|].
      pose proof ND as ND'. rewrite app_assoc in ND'.
      exact (not_eq_sym (nodup_ids_neq _ _ bm b ND' (in_or_app _ _ _ (or_intror INbm)) Hb)). }
    eapply sreach_bind.
    { eapply (membuffer_delete_spec AI AC LOK REALLOCPC) with (ok := Some km) (MB := MB) (idx := idx) (num := num) (A := A) (len := len) (cap := cap)
             (lo := lo) (B := B) (bs := bs) (errv := errv); rewrite ?EQq; try eassumption; try reflexivity; try lia.
      apply mbloc_stack; lia. }
    intros s' LB' ms' PO. unfold membuffer_delete_post in PO.
    destruct PO as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & A' & len' & cap' & ok' & bs'
                    & -> & MI' & ST' & HE' & [errv' ERR'] & HP' & HR' & SUB' & MBC' & LC' & CAP32 & CAPLE & OWN' & FRESH' & RES').
    rewrite EQq in ST', HP'. rewrite RPC.

    assert (LBS : length bs = Z.to_nat (cap + 1)) by (destruct BLKM as [[W0 _] _]; cbn in W0; LiaTuning.ctauto).
    assert (MSG' : exists km', ok' = Some km' /\ nth_error bs' (Z.to_nat len') = Some (Z_to_bv 8 0) /\ (len' = len - num \/ len' = len)%Z).
    { destruct RES' as [(L0 & -> & -> & -> & -> & -> & ->)|[(_ & EL & FN)|(_ & _ & -> & -> & -> & -> & -> & ->)]].
      - exists km. split; [reflexivity|]. split; [| lia]. cbn in NULM. exact NULM.
      - assert (LD : length (del_bytes bs idx num len) = length bs).
        { unfold del_bytes, mm_result. apply upd_bytes_length. rewrite slice_length; lia. }
        destruct ok' as [km'|].
        2:{ cbn in OWN'. destruct OWN' as (_ & _ & ->). exfalso. rewrite firstn_nil in FN. eapply app_cons_not_nil. exact FN. }
        exists km'. split; [reflexivity|]. split; [| lia].
        replace (Z.to_nat (len' + 1)) with (Datatypes.S (Z.to_nat len')) in FN by lia.
        eapply nth_error_firstn_snoc; [exact FN|]. rewrite firstn_length_le; [reflexivity|]. rewrite LD. lia.
      - exists km. split; [reflexivity|]. split; [| lia]. cbn in NULM. rewrite <- NULM. unfold del_bytes, mm_result.
        apply upd_bytes_nth_out; rewrite ?slice_length; lia. }
    destruct MSG' as (km' & -> & NUL' & LEN'). cbn in OWN'. destruct OWN' as [HIN' BLK'].

    assert (TR : forall X0 cs, rw_cells rsegs m X0 cs -> (q <= X0)%Z -> (X0 + Z.of_nat (cells_size cs) <= MB \/ MB + 32 <= X0)%Z -> rw_cells rsegs m' X0 cs).
    { intros X0 cs H H1 H2. eapply (hpx_rw_cells rsegs AI); [exact HP'| exact H| apply client_range_above; lia| cbn; lia]. }

    assert (TRS : forall X0 cs, rw_cells rsegs m X0 cs -> (exists slo shi, al_client_static L_ slo shi /\ slo <= X0 /\ X0 + Z.of_nat (cells_size cs) <= shi)%Z ->
                  (X0 + Z.of_nat (cells_size cs) <= lo)%Z -> rw_cells rsegs m' X0 cs).
    { intros X0 cs H (slo & shi & Hst & S1 & S2) H3. eapply (hpx_rw_cells rsegs AI); [exact HP'| exact H| eapply client_range_static; [exact Hst| lia| lia]| cbn; lia]. }

    pose proof (hpx_heap_pres_low s LB _ m _ q (hl_blocks AI ns hs) m m' HR KSUBH (fun b Hb => lb_keep_sub rsegs AI _ _ _ Hb) HP' ltac:(constructor; [cbn; lia| constructor])) as HPh.
    eapply HK; [| exact LEN'].
    split; [exact HR'|]. split; [exact HE'|]. split; [exact MI'|]. split; [exact ST'|]. split; [eexists; exact ERR'|].
    split; [apply (TR _ _ FSH); cbn; lia|].
    split. { destruct FX as (Q0 & [j16 Q16] & [cz Q20] & (da & db & Q24)).
             split; [apply (TR _ _ Q0); cbn; lia|]. split; [eexists; apply (TR _ _ Q16); cbn; lia|].
             split; [eexists; apply (TR _ _ Q20); cbn; lia| do 2 eexists; apply (TR _ _ Q24); cbn; lia]. }
    split; [unfold p_scan in *; apply (TR _ _ PSC); cbn; lia|].
    split. { split; [exact MBC'|]. split; [cbn; split; [exact HIN'| exact BLK']|]. split; [lia|]. split; [unfold LMAX; lia|]. cbn. exact NUL'. }
    split; [unfold p_ent in *; apply (TR _ _ PENT); cbn; lia|].
    split; [destruct PCTL as [CTL CTLB]; split; [apply (TR _ _ CTL); cbn; lia| exact CTLB]|].
    split. { destruct PHL as (LC & FLC & FF & DL & HS & IT & HB & NB & X0').
             split; [apply (TR _ _ LC); cbn; lia|]. split; [apply (TR _ _ FLC); cbn; lia|]. split; [apply (TR _ _ FF); cbn; lia|].
             split. { eapply (dlseg_heap_pres AI); [exact DL| exact HPh|]. intros b it H. apply in_or_app. left. exact (in_map fst _ _ H). }
             split. { eapply (hdrs_mem_heap_pres AI); [exact HS| exact HPh|]. intros b Hb. apply in_or_app. right. exact Hb. }
             auto. }
    split; [lia|].
    split; [destruct PMETH as [MC MR]; split; [apply (TR _ _ MC); cbn; lia| exact MR]|].
    split; [destruct PVER as ([pad VC] & VR); split; [eexists; apply (TR _ _ VC); cbn; lia| exact VR]|].
    split; [destruct PRS_ as [RC RR]; split; [apply (TR _ _ RC); cbn; lia| exact RR]|].
    split. { intros b Hb. apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [apply SUB'; apply KSUBH; exact Hb|].
             apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [| apply SUB'; apply KSUBK; exact Hb]. cbn in Hb. destruct Hb as [<-|[]]. exact HIN'. }
    split. {
             set (bm' := (km', A', cap' + 1)%Z : BLK).
             assert (NEQ' : forall b, In b (hl_blocks AI ns hs) \/ In b LBK -> blk_id b <> km').
             { intros b Hb E. assert (Hk : In b (lb_keep AI (Some km) LB)) by (destruct Hb as [Hb|Hb]; [apply KSUBH| apply KSUBK]; exact Hb).
               pose proof (FRESH' b Hk) as NE. cbn in NE. apply NE.
               eapply (nodup_ids_eq LB'); [eapply (ai_blocks_nodup rsegs AI); exact HR'| apply SUB'; exact Hk| exact HIN'| exact E]. }
             rewrite !map_app. cbn [map okb app]. rewrite map_app in ND. cbn [map okb app] in ND.
             apply list.NoDup_app in ND. destruct ND as (ND1 & DJ & ND2). inversion ND2 as [|? ? NI ND3]; subst.
             apply list.NoDup_app. split; [exact ND1|]. split.
             - intros x Hx Hin. apply base.list_elem_of_In in Hx. apply in_map_iff in Hx. destruct Hx as (b & <- & Hb).
               apply base.list_elem_of_In in Hin. destruct Hin as [E|Hin]; [exact (NEQ' b (or_introl Hb) (eq_sym E))|].
               apply (DJ (blk_id b)); apply base.list_elem_of_In; [apply in_map; exact Hb| right; exact Hin].
             - constructor; [| exact ND3]. rewrite base.list_elem_of_In. intros Hin. apply in_map_iff in Hin. destruct Hin as (b & E & Hb).
               exact (NEQ' b (or_intror Hb) E). }
    split. { apply (TRS _ _ GM); [| cbn; lia]. destruct GMST as (slo & shi & Hst & G1 & G2). exists slo, shi. split; [exact Hst| cbn; lia]. }
    split. { apply (TRS _ _ IW); [| cbn; lia]. destruct IWST as (slo & shi & Hst & G1 & G2). exists slo, shi. split; [exact Hst| cbn; lia]. }
    split. { eapply (hpx_trans rsegs AI); [exact HPX|]. eapply (hpx_weaken rsegs AI); [exact HP'| | lia| exact KSUBK].
             unfold WE, sub_fp. cbn [outside]. intros; lia. }
    eapply (PHS_hp []); [| exact PH]. eapply (hpx_heap_pres_low s LB _ m _ q [] m m' HR ltac:(intros b []) (fun b Hb => lb_keep_sub rsegs AI _ _ _ Hb) HP').
    constructor; [cbn; lia| constructor].
  Qed.

  #[using="LOK TPV ERRNOV CAN ERRNC BLK4096 BLKIMG GMST IWST TABA ZEROA PHS_munch TABST ZST QLO LO0 CEIL QP PB BHI GMX P8 Q8"] Lemma pe_mchunk : forall gp (F : bvmap 5 word) fc s LB m A len cap km bs ebw elw err hack pos entp clen csz esp ns hs X meth scur xb (rpc : Z)
      t0 t1 t2 a4 a5 a6 a7 s2v s7 t3 t4 t5 t6,
    PC s LB m A len cap (Some km) bs ebw elw err hack pos entp clen csz esp ns hs X meth scur xb -> (0 <= scur <= len)%Z ->
    ret_pc (wz rpc) = wz rpc ->
    (forall m' (r cur' v : Z) (pv : word) t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
        PC s LB m' A len cap (Some km) bs ebw elw err hack pos entp clen csz esp ns hs X meth cur' xb ->
        rw_cells rsegs m' (q + 20) [C4 pv] ->
        (0 <= r <= 5)%Z -> (0 <= cur' <= len)%Z -> (r = 4 -> pv = wz v /\ 0 <= v < 2^31 /\ scur + 1 <= cur')%Z -> (r <> 4 -> cur' = scur) ->
        SREACH AI (pent_post gp F fc) (PRS rpc (wz rpc) t0' t1' t2' (wz r) a1' a2' a3' a4' a5' a6' a7' s2v s7 t3' t4' t5' t6' gp F fc m') s LB) ->
    SREACH AI (pent_post gp F fc) (PRS match_entry (wz rpc) t0 t1 t2 (wz S) (wz FMT_CHUNK) (wz (q + 20)) (wz (q + 24)) a4 a5 a6 a7 s2v s7 t3 t4 t5 t6 gp F fc m) s LB.
  Proof.
    intros until t6. intros INV SCUR RPC HK. pose proof INV as INV0. open_PC INV.
    pose proof P8 as P8z. pose proof Q8 as Q8z. unfold pmod8 in P8z, Q8z.
    pose proof alloc_ceiling_bounds as CE. pose proof alloc_ceiling_aligned8 as CE8.
    assert (EQt : bv_unsigned (wz (al_tp L_)) = al_tp L_) by (rewrite TPV; apply unsigned_lit; lia).
    destruct (msg_facts _ _ _ _ _ _ _ _ HR PMSG) as (HL & HC & A0 & AHI & OKS & _). unfold LMAX in HC.
    destruct (OKS km eq_refl) as (HIN & BLKM & A4 & AW).
    destruct PMSG as (MBC & OWN & HL' & HC' & NULM). cbn in NULM.
    destruct (CAN _ _ _ HR) as [SSP1 [canary SSP2]].
    assert (LBS : length bs = Z.to_nat (cap + 1)) by (destruct BLKM as [[W0 _] _]; cbn in W0; LiaTuning.ctauto).
    pose proof (proj2 (proj1 BLKM)) as BY. cbn [cells_bytes cbytes] in BY. rewrite app_nil_r in BY.
    assert (MOK : vf_ok (q + -64) lo S MB A len cap scur bs) by (unfold vf_ok; lia).
    destruct FX as (Q0 & [j16 Q16] & [cz Q20] & (da & db & Q24)). unfold p_scan in PSC.
    assert (ERRT : rw_cells rsegs m (bv_unsigned (wz (al_tp L_)) - 164) [C4 errv]).
    { rewrite EQt. replace (al_tp L_ - 164)%Z with (al_errno L_) by (rewrite TPV, ERRNOV; reflexivity). exact ERR. }
    eapply sreach_evt.
    { eapply (match_chunk q lo S MB A len cap scur bs MOK (q + 20) (q + 24));
        unfold H_vfmatch_A.SCc, H_vfmatch_A.MBc, H_vfmatch_A.BUFc, got_ssp, ssp_guard; rewrite ?EQt, ?TPV, ?LBS; try eassumption; try LiaTuning.alia.
      rewrite <- TPV. rewrite EQt in ERRT. exact ERRT. }
    intros ms2 PO. unfold mpost in PO.
    destruct PO as (r & cur' & t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2
                    & -> & MU2 & WM2 & MI2 & ST2 & SC2 & MBC2 & BUF2 & RR & CUR' & ROK & RNOK & XC).
    unfold X_chunk, R_chunk in XC. destruct XC as (pv & pa & pb & e2 & (PC2 & PD2 & ERR2 & G2 & C2) & HV).
    rewrite RPC. rewrite ?EQt in MU2. rewrite EQt in ERR2. replace (al_tp L_ - 164)%Z with (al_errno L_) in MU2, ERR2 by (rewrite TPV, ERRNOV; reflexivity).
    unfold H_vfmatch_A.SCc in SC2.

    assert (FW : Forall (wcls []) ((lo, q) :: (S + 8, S + 16) :: [(q + 20, q + 20 + 4); (q + 24, q + 24 + 16); (al_errno L_, al_errno L_ + 4)])%Z).
    { repeat apply Forall_cons; try apply Forall_nil; unfold wcls; cbn -[al_errno]; lia. }
    destruct (seg_ok s LB m m2 _ [] A len cap (Some km) bs ns hs X meth HR HE HPX BSUB ND ltac:(intros b [])
                MU2 WM2 FW FSH (conj Q0 (conj (ex_intro _ j16 Q16) (conj (ex_intro _ cz Q20) (ex_intro _ da (ex_intro _ db Q24)))))
                (conj MBC (conj OWN (conj HL' (conj HC' NULM)))) PHL PMETH PVER PRS_ GM IW PH)
      as (HR2 & HE2 & HP2 & FSH2 & _ & PMETH2 & PVER2 & PRS2 & GM2 & IW2 & PMSG2 & PHL2 & (Q02 & J162) & PH2).
    specialize (PMSG2 ltac:(intros b [])). specialize (PHL2 ltac:(intros b [])).
    pose proof (rw_cells_transport rsegs _ m m2 _ _ PENT MU2 WM2 ltac:(rewrite ERRNOV; cbn; lia)) as PENT2.
    assert (PCTL2 : p_ctl m2 P err hack pos entp clen csz esp).
    { destruct PCTL as [CTL CTLB]. split; [| exact CTLB]. eapply rw_cells_transport; [exact CTL| exact MU2| exact WM2| rewrite ERRNOV; cbn; lia]. }
    assert (HVX : exists v, (r = 4 -> pv = wz v /\ 0 <= v < 2^31 /\ scur + 1 <= cur')%Z).
    { destruct (Z.eq_dec r 4) as [E|NE]; [| exists 0; intros; exfalso; lia]. destruct (HV E) as (v & Ev & VR & CR). exists v. intros _. auto. }
    destruct HVX as [v HVv].
    eapply (HK m2 r cur' v pv); [| exact PC2| exact RR| exact CUR'| exact HVv| exact RNOK].
    split; [exact HR2|]. split; [exact HE2|]. split; [exact MI2|]. split; [exact ST2|]. split; [eexists; exact ERR2|].
    split; [exact FSH2|]. split; [split; [exact Q02| split; [exact J162| split; [eexists; exact PC2| do 2 eexists; exact PD2]]]|].
    split; [exact SC2|]. split; [exact PMSG2|]. split; [exact PENT2|]. split; [exact PCTL2|]. split; [exact PHL2|]. split; [exact XV|].
    split; [exact PMETH2|]. split; [exact PVER2|]. split; [exact PRS2|]. split; [exact BSUB|]. split; [exact ND|].
    split; [exact GM2|]. split; [exact IW2|]. split; [exact HP2| exact PH2].
  Qed.

  Ltac pi1 := first [eassumption | eexists; eassumption | (split; [eassumption| lia]) | lia].
  Ltac mkPI := repeat (split; [pi1|]).

  #[using="LOK ERRNOV ERRNC GMST IWST TABA ZEROA PHS_munch TABST ZST QLO LO0 CEIL QP PB"] Lemma PC_seg : forall s LB m m' W A len cap okm bs ebw elw err hack pos entp clen csz esp ns hs X meth scur xb
      (ebw' elw' : word) (err' hack' pos' entp' clen' csz' esp' scur' : Z),
    PC s LB m A len cap okm bs ebw elw err hack pos entp clen csz esp ns hs X meth scur xb ->
    munch W m m' -> wmono rsegs m m' -> mem_inv rsegs m' -> Forall (wcls []) W ->
    Forall (fun iv => snd iv <= q + 20 \/ q + 40 <= fst iv)%Z W ->
    Forall (fun iv => al_errno L_ + 4 <= fst iv)%Z W ->
    (Forall (fun iv => q <= fst iv)%Z W \/ stk rsegs m' lo q) ->
    p_scan m' P scur' -> p_ent m' P ebw' elw' -> p_ctl m' P err' hack' pos' entp' clen' csz' esp' ->
    PC s LB m' A len cap okm bs ebw' elw' err' hack' pos' entp' clen' csz' esp' ns hs X meth scur' xb.
  Proof.
    intros until scur'. intros INV MU WM MI' FW FW5 FWE STH SC' ENT' CTL'. open_PC INV.
    destruct (seg_ok s LB m m' W [] A len cap okm bs ns hs X meth HR HE HPX BSUB ND ltac:(intros b []) MU WM FW FSH FX PMSG PHL PMETH PVER PRS_ GM IW PH)
      as (HR2 & HE2 & HP2 & FSH2 & FX2 & PMETH2 & PVER2 & PRS2 & GM2 & IW2 & PMSG2 & PHL2 & _ & PH2).
    specialize (FX2 FW5). specialize (PMSG2 ltac:(intros b [])). specialize (PHL2 ltac:(intros b [])).
    pose proof (rw_cells_transport rsegs _ m m' _ _ ERR MU WM ltac:(apply disjoint_from_Forall; eapply Forall_impl; [| exact FWE]; cbn; intros [l h] Hl; cbn in *; lia)) as ERR2.
    assert (ST2 : stk rsegs m' lo q).
    { destruct STH as [FWQ|ST']; [| exact ST']. eapply (stk_transport_disjoint rsegs); [exact ST| exact MU| exact WM|].
      apply disjoint_from_Forall. eapply Forall_impl; [| exact FWQ]. cbn. intros [l h] Hl; cbn in *. lia. }
    split; [exact HR2|]. split; [exact HE2|]. split; [exact MI'|]. split; [exact ST2|]. split; [eexists; exact ERR2|].
    split; [exact FSH2|]. split; [exact FX2|]. split; [exact SC'|]. split; [exact PMSG2|]. split; [exact ENT'|]. split; [exact CTL'|].
    split; [exact PHL2|]. split; [exact XV|]. split; [exact PMETH2|]. split; [exact PVER2|]. split; [exact PRS2|].
    split; [exact BSUB|]. split; [exact ND|]. split; [exact GM2|]. split; [exact IW2|]. split; [exact HP2| exact PH2].
  Qed.

  #[using="AC LOK REALLOCPC TPV ERRNOV CAN ERRNC BLK4096 BLKIMG GMST IWST TABA ZEROA PHS_munch PHS_hp TABST ZST QLO QLO2 STK0 LO0 CEIL QP PB BHI GMX P8 Q8"] Lemma pe_case3 : forall M gp F fc s LB m cur A len cap km bs ebw elw err hack pos entp clen csz esp ns hs X meth
      t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 t3 t4 t5 t6 x1,
    CONT M gp F fc -> PI s LB m cur A len cap (Some km) bs ebw elw err hack pos entp clen csz esp ns hs X meth -> entp = 3 -> M = pe_meas entp elw ->
    SREACH AI (pent_post gp F fc) (PRS 0x157d0 x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (wz S) s7 t3 t4 t5 t6 gp F fc m) s LB.
  Proof.
    intros until x1. intros HC INV E3 HM. subst entp.
    pose proof alloc_ceiling_bounds as CE. pose proof alloc_ceiling_aligned8 as CE8.
    assert (EQq : bv_unsigned (wz q) = q) by (apply unsigned_lit; lia).
    destruct (PI_PC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ INV) as (PCI & CUR & EOK).
    pose proof PCI as PCI0. open_PC PCI.
    destruct (msg_facts _ _ _ _ _ _ _ _ HR PMSG) as (HL & HCAP & A0 & AHI & _). unfold LMAX in HCAP.
    destruct EOK as (ESP & ELEN & _). specialize (ESP ltac:(lia)). destruct (ELEN ltac:(lia)) as (elen & -> & ELR).
    destruct PCTL as [CTL CTLB].

    eapply sreach_evt. { rewrite TPV. apply (pe_chunk1 P q cur); [exact MI| exact PSC| lia]. }
    intros ms1 ->. rewrite <- TPV. try clear HR; try clear HE; try clear MI; try clear ST; try clear ERR; try clear FSH; try clear FX; try clear PSC; try clear PMSG; try clear PENT; try clear PCTL; try clear CTL; try clear CTLB; try clear PHL; try clear XV; try clear PMETH; try clear PVER; try clear PRS_; try clear BSUB; try clear ND; try clear GM; try clear IW; try clear HPX; try clear PH; try clear errv.

    eapply (pe_mchunk gp F fc s LB m A len cap km bs ebw (wz elen) err hack pos 3 clen csz esp ns hs X meth cur cur 0x157e8);
      [exact PCI0| exact CUR| apply ret_pc_even; [lia| reflexivity]|]. clear PCI0.
    intros m2 r cur' v pv t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' PC2 PCV RR CUR' HV RNV.
    pose proof PC2 as PC20. open_PC PC2. destruct PCTL as [CTL CTLB]. destruct FX as (Q0 & J16 & _). unfold p_scan in PSC.

    eapply sreach_evt.
    { rewrite TPV. eapply (pe_chunk2 P q QP PHI63 r v cur' cur csz esp err hack pos 3 clen pv); unfold ctl9; try eassumption; try LiaTuning.alia.
      intros E. destruct (HV E) as (Epv & VR & _). split; [exact Epv| exact VR]. }
    intros ms3 (m3 & ALT & WM3 & MI3 & PCV3 & Q03).
    destruct ALT as [(NR & -> & MU3 & SC3 & CTL3)|(R4 & -> & MU3 & SC3 & CTL3)]; rewrite <- TPV.
    -
      pose proof (PC_seg s LB m2 m3 _ A len cap (Some km) bs ebw (wz elen) err hack pos 3 clen csz esp ns hs X meth cur' cur ebw (wz elen) err hack pos 3 clen csz esp cur
                    PC20 MU3 WM3 MI3 ltac:(repeat apply Forall_cons; try apply Forall_nil; unfold wcls; cbn; lia)
                    ltac:(repeat apply Forall_cons; try apply Forall_nil; cbn; lia) ltac:(repeat apply Forall_cons; try apply Forall_nil; rewrite ERRNOV; cbn; lia)
                    ltac:(left; repeat apply Forall_cons; try apply Forall_nil; cbn; lia)
                    SC3 ltac:(eapply rw_cells_transport; [exact PENT| exact MU3| exact WM3| cbn; lia]) (conj CTL3 CTLB)) as PC3.
      try clear HR; try clear HE; try clear MI; try clear ST; try clear ERR; try clear FSH; try clear FX; try clear PSC; try clear PMSG; try clear PENT; try clear PCTL; try clear CTL; try clear CTLB; try clear PHL; try clear XV; try clear PMETH; try clear PVER; try clear PRS_; try clear BSUB; try clear ND; try clear GM; try clear IW; try clear HPX; try clear PH; try clear errv. clear PC20 MU3 WM3 SC3 CTL3 PCV3 Q03. pose proof PC3 as PC30. open_PC PC3.
      eapply sreach_evt. { rewrite TPV. eapply (UpnpPrintf_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m3 lo); rewrite ?EQq; [exact IW| exact ST| lia| lia| exact MI]. }
      intros ms4 PO. unfold UpnpPrintf_post in PO.
      destruct PO as (u0 & u1 & u2 & v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m4 & -> & MU4 & WM4 & MI4 & ST4 & IW4). rewrite EQq in MU4, ST4. rewrite <- TPV.
      replace (ret_pc (wz 0x158c8)) with (wz 0x158c8 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      pose proof (PC_seg s LB m3 m4 _ A len cap (Some km) bs ebw (wz elen) err hack pos 3 clen csz esp ns hs X meth cur cur ebw (wz elen) err hack pos 3 clen csz esp cur
                    PC30 MU4 WM4 MI4 ltac:(repeat apply Forall_cons; try apply Forall_nil; unfold wcls; cbn; lia)
                    ltac:(repeat apply Forall_cons; try apply Forall_nil; cbn; lia) ltac:(repeat apply Forall_cons; try apply Forall_nil; rewrite ERRNOV; cbn; lia) (or_intror ST4)
                    ltac:(eapply rw_cells_transport; [exact PSC| exact MU4| exact WM4| cbn; lia])
                    ltac:(eapply rw_cells_transport; [exact PENT| exact MU4| exact WM4| cbn; lia])
                    ltac:(split; [eapply rw_cells_transport; [exact (proj1 PCTL)| exact MU4| exact WM4| cbn; lia]| exact (proj2 PCTL)])) as PC4.
      try clear HR; try clear HE; try clear MI; try clear ST; try clear ERR; try clear FSH; try clear FX; try clear PSC; try clear PMSG; try clear PENT; try clear PCTL; try clear CTL; try clear CTLB; try clear PHL; try clear XV; try clear PMETH; try clear PVER; try clear PRS_; try clear BSUB; try clear ND; try clear GM; try clear IW; try clear HPX; try clear PH; try clear errv. clear PC30 MU4 WM4 MI4 ST4 IW4.
      eapply sreach_evt. { rewrite TPV. apply (pe_chunk3 P q r). }
      intros ms5 ->. rewrite <- TPV.
      eapply (pe_cont M gp F fc s LB m4 cur A len cap km bs ebw (wz elen) err hack pos 3 clen csz esp ns hs X meth r); [exact HC| | lia| exact NR| intros; exfalso; lia].
      eapply PC_PI; [exact PC4| lia| lia|]. unfold ent_ok. split; [intros; lia|]. split; [intros _; exists elen; split; [reflexivity| lia]| intros; lia].
    -
      destruct (HV R4) as (-> & VR & CR).
      assert (PCTL3 : p_ctl m3 P err hack pos 3 clen v esp) by (split; [exact CTL3| lia]).
      pose proof (PC_seg s LB m2 m3 _ A len cap (Some km) bs ebw (wz elen) err hack pos 3 clen csz esp ns hs X meth cur' cur ebw (wz elen) err hack pos 3 clen v esp cur'
                    PC20 MU3 WM3 MI3 ltac:(repeat apply Forall_cons; try apply Forall_nil; unfold wcls; cbn; lia)
                    ltac:(repeat apply Forall_cons; try apply Forall_nil; cbn; lia) ltac:(repeat apply Forall_cons; try apply Forall_nil; rewrite ERRNOV; cbn; lia)
                    ltac:(left; repeat apply Forall_cons; try apply Forall_nil; cbn; lia)
                    SC3 ltac:(eapply rw_cells_transport; [exact PENT| exact MU3| exact WM3| cbn; lia]) PCTL3) as PC3. clear PCTL3.
      try clear HR; try clear HE; try clear MI; try clear ST; try clear ERR; try clear FSH; try clear FX; try clear PSC; try clear PMSG; try clear PENT; try clear PCTL; try clear CTL; try clear CTLB; try clear PHL; try clear XV; try clear PMETH; try clear PVER; try clear PRS_; try clear BSUB; try clear ND; try clear GM; try clear IW; try clear HPX; try clear PH; try clear errv. clear PC20 MU3 WM3 SC3 CTL3 PCV3 Q03.
      eapply (pe_mdel gp F fc s LB m3 A len cap km bs ebw (wz elen) err hack pos 3 clen v esp ns hs X meth cur' cur cur (cur' - cur) 0x15808);
        [exact PC3| lia| lia| lia| apply ret_pc_even; [lia| reflexivity]|]. clear PC3.
      intros s4 LB4 m4 A' len' cap' km' bs' u0 u1 u2 v0 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 PC4 LEN4.
      pose proof PC4 as PC40. open_PC PC4. destruct PCTL as [CTL CTLB]. destruct PVER as ([pad VERC] & VERB). unfold p_scan in PSC. unfold p_ent in PENT.
      destruct (msg_facts _ _ _ _ _ _ _ _ HR PMSG) as (HL4 & HCAP4 & A04 & AHI4 & _).
      eapply sreach_evt.
      { rewrite TPV. eapply (pe_chunk4 P q lo QLO1 LO0 QP PHI63 v cur' cur esp err hack pos 3 clen gmax isreq maj min ebw (wz elen) pad); unfold ctl9; try eassumption; try LiaTuning.alia. }
      intros ms5 (m5 & r5 & err' & entp' & el' & a0'' & a1'' & -> & -> & MU5 & WM5 & MI5 & SC5 & CTL5 & VER5 & ENT5 & GM5 & RES5). rewrite <- TPV.
      assert (RB : (0 <= err' < 2^31)%Z /\ (0 <= entp' <= 6)%Z /\ exists elw', el' = C8 elw').
      { destruct RES5 as [(_ & _ & -> & -> & ->)|[(_ & _ & -> & -> & ->)|(_ & _ & -> & -> & ->)]]; (split; [lia| split; [lia| eexists; reflexivity]]). }
      destruct RB as (ERB & ENB & [elw' Eel]). rewrite Eel in ENT5.
      assert (PCTL5 : p_ctl m5 P err' hack pos entp' clen v esp) by (split; [exact CTL5| lia]).
      pose proof (PC_seg s4 LB4 m4 m5 _ A' len' cap' (Some km') bs' ebw (wz elen) err hack pos 3 clen v esp ns hs X meth cur' (Z.min cur len') ebw elw' err' hack pos entp' clen v esp cur
                    PC40 MU5 WM5 MI5 ltac:(repeat apply Forall_cons; try apply Forall_nil; unfold wcls; cbn; lia)
                    ltac:(repeat apply Forall_cons; try apply Forall_nil; cbn; lia) ltac:(repeat apply Forall_cons; try apply Forall_nil; rewrite ERRNOV; cbn; lia)
                    ltac:(left; repeat apply Forall_cons; try apply Forall_nil; cbn; lia)
                    SC5 ENT5 PCTL5) as PC5. clear PCTL5.
      try clear HR; try clear HE; try clear MI; try clear ST; try clear ERR; try clear FSH; try clear FX; try clear PSC; try clear PMSG; try clear PENT; try clear PCTL; try clear CTL; try clear CTLB; try clear PHL; try clear XV; try clear PMETH; try clear PVER; try clear PRS_; try clear BSUB; try clear ND; try clear GM; try clear IW; try clear HPX; try clear PH; try clear errv. clear PC40 MU5 WM5 SC5 CTL5 VER5 ENT5 GM5.
      assert (EL : elen_of (wz elen) = elen) by (unfold elen_of; apply unsigned_lit; lia).
      destruct RES5 as [(V0 & -> & -> & -> & EE)|[(VR1 & -> & -> & -> & EE)|(VG & -> & -> & -> & EE)]];
        (assert (EW : elw' = match el' with C8 w => w | _ => elw' end) by (rewrite Eel; reflexivity)); rewrite EE in EW; cbn in EW; subst elw'.
      +
        eapply (pe_cont M gp F fc s4 LB4 m5 cur A' len' cap' km' bs' ebw (wz (cur - esp)) err hack pos 6 clen v esp ns hs X meth 6); [exact HC| | lia| lia|].
        * eapply PC_PI; [exact PC5| lia| lia|]. unfold ent_ok. repeat split; intros; lia.
        * intros _. rewrite HM. unfold pe_meas. cbn [Z.eqb Pos.eqb]. rewrite EL. lia.
      +
        eapply (pe_cont M gp F fc s4 LB4 m5 cur A' len' cap' km' bs' ebw (wz elen) err hack pos 5 clen v esp ns hs X meth 6); [exact HC| | lia| lia|].
        * eapply PC_PI; [exact PC5| lia| lia|]. unfold ent_ok. split; [intros; lia|]. split; [intros _; exists elen; split; [reflexivity| lia]| intros; lia].
        * intros _. rewrite HM. unfold pe_meas. cbn [Z.eqb Pos.eqb]. rewrite EL. lia.
      +
        eapply (pe_cont M gp F fc s4 LB4 m5 cur A' len' cap' km' bs' ebw (wz elen) 413 hack pos 3 clen v esp ns hs X meth 3); [exact HC| | lia| lia| intros; exfalso; lia].
        eapply PC_PI; [exact PC5| lia| lia|]. unfold ent_ok. split; [intros; lia|]. split; [intros _; exists elen; split; [reflexivity| lia]| intros; lia].
  Qed.

  #[using="LOK ERRNOV ERRNC BLK4096 BLKIMG GMST IWST TABA ZEROA PHS_munch TABST ZST QLO LO0 CEIL QP PB BHI GMX P8 Q8"] Lemma pe_mcrlf : forall gp (F : bvmap 5 word) fc s LB m A len cap km bs ebw elw err hack pos entp clen csz esp ns hs X meth scur xb (rpc : Z)
      t0 t1 t2 a2 a3 a4 a5 a6 a7 s2v s7 t3 t4 t5 t6,
    PC s LB m A len cap (Some km) bs ebw elw err hack pos entp clen csz esp ns hs X meth scur xb -> (0 <= scur <= len)%Z ->
    ret_pc (wz rpc) = wz rpc ->
    (forall m' (r cur' : Z) t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
        PC s LB m' A len cap (Some km) bs ebw elw err hack pos entp clen csz esp ns hs X meth cur' xb ->
        (0 <= r <= 5)%Z -> (0 <= cur' <= len)%Z -> (r = 4 -> scur + 1 <= cur')%Z -> (r <> 4 -> cur' = scur) ->
        SREACH AI (pent_post gp F fc) (PRS rpc (wz rpc) t0' t1' t2' (wz r) a1' a2' a3' a4' a5' a6' a7' s2v s7 t3' t4' t5' t6' gp F fc m') s LB) ->
    SREACH AI (pent_post gp F fc) (PRS match_entry (wz rpc) t0 t1 t2 (wz S) (wz FMT_CRLF) a2 a3 a4 a5 a6 a7 s2v s7 t3 t4 t5 t6 gp F fc m) s LB.
  Proof.
    intros until t6. intros INV SCUR RPC HK. pose proof INV as INV0. open_PC INV.
    pose proof P8 as P8z. pose proof Q8 as Q8z. unfold pmod8 in P8z, Q8z.
    pose proof alloc_ceiling_bounds as CE. pose proof alloc_ceiling_aligned8 as CE8.
    destruct (msg_facts _ _ _ _ _ _ _ _ HR PMSG) as (HL & HC & A0 & AHI & OKS & _). unfold LMAX in HC.
    destruct (OKS km eq_refl) as (HIN & BLKM & A4 & AW).
    destruct PMSG as (MBC & OWN & HL' & HC' & NULM). cbn in NULM.
    assert (LBS : length bs = Z.to_nat (cap + 1)) by (destruct BLKM as [[W0 _] _]; cbn in W0; LiaTuning.ctauto).
    pose proof (proj2 (proj1 BLKM)) as BY. cbn [cells_bytes cbytes] in BY. rewrite app_nil_r in BY.
    assert (MOK : vf_ok (q + -64) lo S MB A len cap scur bs) by (unfold vf_ok; lia).
    unfold p_scan in PSC.
    eapply sreach_evt.
    { eapply (match_crlf2 q lo S MB A len cap scur bs MOK); unfold H_vfmatch_A.SCc, H_vfmatch_A.MBc, H_vfmatch_A.BUFc; try eassumption. }
    intros ms2 PO. unfold mpost in PO.
    destruct PO as (r & cur' & t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2
                    & -> & MU2 & WM2 & MI2 & ST2 & SC2 & MBC2 & BUF2 & RR & CUR' & ROK & RNOK & [_ HOK]).
    rewrite RPC. unfold H_vfmatch_A.SCc in SC2.
    pose proof (PC_seg s LB m m2 _ A len cap (Some km) bs ebw elw err hack pos entp clen csz esp ns hs X meth scur xb ebw elw err hack pos entp clen csz esp cur'
                  INV0 MU2 WM2 MI2 ltac:(repeat apply Forall_cons; try apply Forall_nil; unfold wcls; cbn; lia)
                  ltac:(repeat apply Forall_cons; try apply Forall_nil; cbn; lia)
                  ltac:(destruct (lo_errno_img rsegs AI LOK) as (we & Hwe & WE1 & WE2); pose proof (lo_img_ceiling rsegs AI LOK we Hwe);
                        repeat apply Forall_cons; try apply Forall_nil; cbn -[alloc_ceiling]; lia)
                  (or_intror ST2) SC2
                  ltac:(eapply rw_cells_transport; [exact PENT| exact MU2| exact WM2| cbn; lia])
                  ltac:(split; [eapply rw_cells_transport; [exact (proj1 PCTL)| exact MU2| exact WM2| cbn; lia]| exact (proj2 PCTL)])) as PC2.
    eapply (HK m2 r cur'); [exact PC2| exact RR| exact CUR'| exact HOK| exact RNOK].
  Qed.

  #[using="AC LOK REALLOCPC TPV ERRNOV ERRNC BLK4096 BLKIMG GMST IWST TABA ZEROA PHS_munch PHS_hp TABST ZST QLO QLO2 STK0 LO0 CEIL QP PB BHI GMX P8 Q8"] Lemma pe_case5 : forall M gp F fc s LB m cur A len cap km bs ebw elw err hack pos entp clen csz esp ns hs X meth
      t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 t3 t4 t5 t6 x1,
    CONT M gp F fc -> PI s LB m cur A len cap (Some km) bs ebw elw err hack pos entp clen csz esp ns hs X meth -> entp = 5 -> M = pe_meas entp elw ->
    SREACH AI (pent_post gp F fc) (PRS 0x15834 x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (wz S) s7 t3 t4 t5 t6 gp F fc m) s LB.
  Proof.
    intros until x1. intros HC INV E5 HM. subst entp.
    pose proof alloc_ceiling_bounds as CE. pose proof alloc_ceiling_aligned8 as CE8.
    destruct (PI_PC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ INV) as (PCI & CUR & EOK).
    pose proof PCI as PCI0. open_PC PCI.
    destruct (msg_facts _ _ _ _ _ _ _ _ HR PMSG) as (HL & HCAP & A0 & AHI & _). unfold LMAX in HCAP.
    destruct EOK as (ESP & ELEN & CSZ). specialize (ESP ltac:(lia)). destruct (ELEN ltac:(lia)) as (elen & -> & ELR). specialize (CSZ eq_refl).
    destruct PCTL as [CTL CTLB]. destruct PMSG as (MBC & PMSG'). unfold p_scan in PSC.

    eapply sreach_evt.
    { rewrite TPV. eapply (pe_body1 P q PHI63 A len cap cur csz esp err hack pos 5 clen); unfold ctl9; try eassumption; try LiaTuning.alia. }
    intros ms1 (m1 & a1' & [(LT & -> & -> & SC1)|(GE & -> & MU1 & WM1 & MI1 & SC1 & MBC1 & CTL1)]); rewrite <- TPV.
    {   eapply pe_exit; [exact INV| lia| lia]. }
    pose proof (PC_seg s LB m m1 _ A len cap (Some km) bs ebw (wz elen) err hack pos 5 clen csz esp ns hs X meth cur cur ebw (wz elen) err hack pos 5 clen csz esp (cur + csz)
                  PCI0 MU1 WM1 MI1 ltac:(repeat apply Forall_cons; try apply Forall_nil; unfold wcls; cbn; lia)
                  ltac:(repeat apply Forall_cons; try apply Forall_nil; cbn; lia) ltac:(repeat apply Forall_cons; try apply Forall_nil; rewrite ERRNOV; cbn; lia)
                  ltac:(left; repeat apply Forall_cons; try apply Forall_nil; cbn; lia)
                  SC1 ltac:(eapply rw_cells_transport; [exact PENT| exact MU1| exact WM1| cbn; lia]) (conj CTL1 CTLB)) as PC1.
    try clear HR; try clear HE; try clear MI; try clear ST; try clear ERR; try clear FSH; try clear FX; try clear PSC; try clear PMSG; try clear PENT; try clear PCTL; try clear CTL; try clear CTLB; try clear PHL; try clear XV; try clear PMETH; try clear PVER; try clear PRS_; try clear BSUB; try clear ND; try clear GM; try clear IW; try clear HPX; try clear PH; try clear errv; clear MBC PMSG' PCI0 MU1 WM1 MI1 SC1 MBC1 CTL1.

    eapply (pe_mcrlf gp F fc s LB m1 A len cap km bs ebw (wz elen) err hack pos 5 clen csz esp ns hs X meth (cur + csz) cur 0x1585c);
      [exact PC1| lia| apply ret_pc_even; [lia| reflexivity]|]. clear PC1.
    intros m2 r cur' t0' t1' t2' b1 b2 b3 b4 b5 b6 b7 t3' t4' t5' t6' PC2 RR CUR' HOK RNOK.
    pose proof PC2 as PC20. open_PC PC2. destruct PCTL as [CTL CTLB]. unfold p_scan in PSC.

    eapply sreach_evt.
    { rewrite TPV. eapply (pe_body2 P q PHI63 r cur' (cur + csz) csz esp err hack pos 5 clen); unfold ctl9; try eassumption; try LiaTuning.alia. }
    intros ms3 (m3 & c1 & c2 & [(NR & -> & MU3 & WM3 & MI3 & SC3 & CTL3)|(R4 & -> & ->)]); rewrite <- TPV.
    -
      rewrite (RNOK NR) in SC3. replace (cur + csz - csz)%Z with cur in SC3 by lia.
      pose proof (PC_seg s LB m2 m3 _ A len cap (Some km) bs ebw (wz elen) err hack pos 5 clen csz esp ns hs X meth cur' cur ebw (wz elen) err hack pos 5 clen csz esp cur
                    PC20 MU3 WM3 MI3 ltac:(repeat apply Forall_cons; try apply Forall_nil; unfold wcls; cbn; lia)
                    ltac:(repeat apply Forall_cons; try apply Forall_nil; cbn; lia) ltac:(repeat apply Forall_cons; try apply Forall_nil; rewrite ERRNOV; cbn; lia)
                    ltac:(left; repeat apply Forall_cons; try apply Forall_nil; cbn; lia)
                    SC3 ltac:(eapply rw_cells_transport; [exact PENT| exact MU3| exact WM3| cbn; lia]) (conj CTL3 CTLB)) as PC3.
      eapply pe_exitC; [exact PC3| lia| lia| exact NR].
    -
      pose proof (HOK R4) as CR.
      try clear HR; try clear HE; try clear MI; try clear ST; try clear ERR; try clear FSH; try clear FX; try clear PSC; try clear PMSG; try clear PENT; try clear PCTL; try clear CTL; try clear CTLB; try clear PHL; try clear XV; try clear PMETH; try clear PVER; try clear PRS_; try clear BSUB; try clear ND; try clear GM; try clear IW; try clear HPX; try clear PH; try clear errv.
      eapply (pe_mdel gp F fc s LB m2 A len cap km bs ebw (wz elen) err hack pos 5 clen csz esp ns hs X meth cur' cur (cur + csz) (cur' - (cur + csz)) 0x15874);
        [exact PC20| lia| lia| lia| apply ret_pc_even; [lia| reflexivity]|]. clear PC20.
      intros s4 LB4 m4 A' len' cap' km' bs' u0 u1 u2 v0 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 PC4 LEN4.
      pose proof PC4 as PC40. open_PC PC4. destruct PCTL as [CTL CTLB]. unfold p_scan in PSC. unfold p_ent in PENT.
      destruct (msg_facts _ _ _ _ _ _ _ _ HR PMSG) as (HL4 & HCAP4 & A04 & AHI4 & _).

      eapply sreach_evt.
      { rewrite TPV. eapply (pe_body3 P q lo QLO1 LO0 QP PHI63 csz cur' (cur + csz) esp err hack pos 5 clen gmax elen ebw); unfold ctl9; try eassumption; try LiaTuning.alia. }
      intros ms5 (m5 & r5 & err' & entp' & a0'' & a1'' & a2'' & pc & -> & -> & MU5 & WM5 & MI5 & SC5 & CTL5 & ENT5 & GM5 & RES5). rewrite <- TPV.
      assert (RB : (0 <= err' < 2^31)%Z /\ (0 <= entp' <= 6)%Z) by (destruct RES5 as [(_ & _ & _ & -> & ->)|(_ & _ & _ & -> & ->)]; lia).
      destruct RB as [ERB ENB].
      assert (PCTL5 : p_ctl m5 P err' hack pos entp' clen csz esp) by (split; [exact CTL5| lia]).
      pose proof (PC_seg s4 LB4 m4 m5 _ A' len' cap' (Some km') bs' ebw (wz elen) err hack pos 5 clen csz esp ns hs X meth cur' (Z.min cur len') ebw (wz (elen + csz)) err' hack pos entp' clen csz esp (cur + csz)
                    PC40 MU5 WM5 MI5 ltac:(repeat apply Forall_cons; try apply Forall_nil; unfold wcls; cbn; lia)
                    ltac:(repeat apply Forall_cons; try apply Forall_nil; cbn; lia) ltac:(repeat apply Forall_cons; try apply Forall_nil; rewrite ERRNOV; cbn; lia)
                    ltac:(left; repeat apply Forall_cons; try apply Forall_nil; cbn; lia)
                    SC5 ENT5 PCTL5) as PC5. clear PCTL5.
      try clear HR; try clear HE; try clear MI; try clear ST; try clear ERR; try clear FSH; try clear FX; try clear PSC; try clear PMSG; try clear PENT; try clear PCTL; try clear CTL; try clear CTLB; try clear PHL; try clear XV; try clear PMETH; try clear PVER; try clear PRS_; try clear BSUB; try clear ND; try clear GM; try clear IW; try clear HPX; try clear PH; try clear errv.
      assert (EL : elen_of (wz elen) = elen) by (unfold elen_of; apply unsigned_lit; lia).
      destruct RES5 as [(LE & -> & -> & -> & ->)|(GT & -> & -> & -> & ->)].
      +
        eapply (pe_cont M gp F fc s4 LB4 m5 (cur + csz) A' len' cap' km' bs' ebw (wz (elen + csz)) err hack pos 3 clen csz esp ns hs X meth 6); [exact HC| | lia| lia|].
        * eapply PC_PI; [exact PC5| lia| lia|]. unfold ent_ok. split; [intros; lia|]. split; [intros _; exists (elen + csz)%Z; split; [reflexivity| lia]| intros; lia].
        * intros _. rewrite HM. unfold pe_meas. cbn [Z.eqb Pos.eqb]. rewrite EL. unfold elen_of. rewrite unsigned_lit by lia. lia.
      +
        eapply pe_exitC; [exact PC5| lia| lia| lia].
  Qed.

  #[using="AC LOK REALLOCPC TPV ERRNOV ERRNC BLK4096 BLKIMG GMST IWST TABA ZEROA PHS_munch PHS_hp TABST ZST QLO QLO2 STK0 LO0 CEIL QP PB BHI GMX P8 Q8 HCALL"] Lemma pe_case6 : forall gp F fc s LB m cur A len cap km bs ebw elw err hack pos entp clen csz esp ns hs X meth
      t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 t3 t4 t5 t6 x1,
    PI s LB m cur A len cap (Some km) bs ebw elw err hack pos entp clen csz esp ns hs X meth -> entp = 6 ->
    SREACH AI (pent_post gp F fc) (PRS 0x15968 x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (wz S) s7 t3 t4 t5 t6 gp F fc m) s LB.
  Proof.
    intros until x1. intros INV E6. subst entp.
    pose proof alloc_ceiling_bounds as CE. pose proof alloc_ceiling_aligned8 as CE8.
    destruct (PI_PC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ INV) as (PCI & CUR & EOK).
    pose proof PCI as PCI0. open_PC PCI.
    destruct (msg_facts _ _ _ _ _ _ _ _ HR PMSG) as (HL & HCAP & A0 & AHI & _). unfold LMAX in HCAP.
    destruct EOK as (ESP & _ & _). specialize (ESP ltac:(lia)). unfold p_scan in PSC.

    eapply sreach_evt. { rewrite TPV. apply (pe_hdr1 P q cur); [exact MI| exact PSC| lia]. }
    intros ms1 ->. rewrite <- TPV.
    try clear HR; try clear HE; try clear MI; try clear ST; try clear ERR; try clear FSH; try clear FX; try clear PSC; try clear PMSG; try clear PENT; try clear PCTL; try clear CTL; try clear CTLB; try clear PHL; try clear XV; try clear PMETH; try clear PVER; try clear PRS_; try clear BSUB; try clear ND; try clear GM; try clear IW; try clear HPX; try clear PH; try clear errv.

    eapply (HCALL gp F fc s LB m A len cap km bs ebw elw err hack pos 6 clen csz esp ns hs X meth cur 0x15974); [exact PCI0| exact CUR| apply ret_pc_even; [lia| reflexivity]|].
    clear PCI0. intros s2 LB2 m2 r cur' meth' err' pos' X' ns' hs' t0' t1' t2' b1 b2 b3 b4 b5 b6 b7 t3' t4' t5' t6' PC2 RR CUR'.
    pose proof PC2 as PC20. open_PC PC2. destruct PCTL as [CTL CTLB]. unfold p_scan in PSC.

    eapply sreach_evt.
    { rewrite TPV. eapply (pe_hdr2 P q PHI63 r cur' cur err' hack pos' 6 clen csz esp); unfold ctl9; try eassumption; try LiaTuning.alia. }
    intros ms3 (m3 & c1 & [(NR & -> & ->)|(R4 & -> & MU3 & WM3 & MI3 & SC3 & CTL3)]); rewrite <- TPV.
    { eapply pe_exitC; [exact PC20| lia| lia| exact NR]. }

    assert (PCTL3 : p_ctl m3 P err' hack 4 6 clen csz esp) by (split; [exact CTL3| lia]).
    pose proof (PC_seg s2 LB2 m2 m3 _ A len cap (Some km) bs ebw elw err' hack pos' 6 clen csz esp ns' hs' X' meth' cur' cur' ebw elw err' hack 4 6 clen csz esp cur'
                  PC20 MU3 WM3 MI3 ltac:(repeat apply Forall_cons; try apply Forall_nil; unfold wcls; cbn; lia)
                  ltac:(repeat apply Forall_cons; try apply Forall_nil; cbn; lia) ltac:(repeat apply Forall_cons; try apply Forall_nil; rewrite ERRNOV; cbn; lia)
                  ltac:(left; repeat apply Forall_cons; try apply Forall_nil; cbn; lia)
                  SC3 ltac:(eapply rw_cells_transport; [exact PENT| exact MU3| exact WM3| cbn; lia]) PCTL3) as PC3. clear PCTL3.
    try clear HR; try clear HE; try clear MI; try clear ST; try clear ERR; try clear FSH; try clear FX; try clear PSC; try clear PMSG; try clear PENT; try clear PCTL; try clear CTL; try clear CTLB; try clear PHL; try clear XV; try clear PMETH; try clear PVER; try clear PRS_; try clear BSUB; try clear ND; try clear GM; try clear IW; try clear HPX; try clear PH; try clear errv.
    clear PC20 MU3 WM3 SC3 CTL3.
    eapply (pe_mdel gp F fc s2 LB2 m3 A len cap km bs ebw elw err' hack 4 6 clen csz esp ns' hs' X' meth' cur' cur' cur (cur' - cur) 0x15994);
      [exact PC3| lia| lia| lia| apply ret_pc_even; [lia| reflexivity]|]. clear PC3.
    intros s4 LB4 m4 A' len' cap' km' bs' u0 u1 u2 v0 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 PC4 LEN4.
    pose proof PC4 as PC40. open_PC PC4. destruct PCTL as [CTL CTLB]. unfold p_scan in PSC. unfold p_ent in PENT. destruct PMSG as (MBC & PMSG').
    destruct (msg_facts _ _ _ _ _ _ _ _ HR (conj MBC PMSG')) as (HL4 & HCAP4 & A04 & AHI4 & OKS4 & _).
    destruct (OKS4 km' eq_refl) as (_ & _ & A4' & _).

    eapply sreach_evt.
    { rewrite TPV. eapply (pe_hdr3 P q PHI63 A' len' cap' cur' cur esp err' hack 4 6 clen csz ebw elw); unfold ctl9; try eassumption; try LiaTuning.alia. }
    intros ms5 (m5 & a1'' & a2'' & -> & MU5 & WM5 & MI5 & SC5 & MBC5 & CTL5 & ENT5). rewrite <- TPV.
    pose proof (PC_seg s4 LB4 m4 m5 _ A' len' cap' (Some km') bs' ebw elw err' hack 4 6 clen csz esp ns' hs' X' meth' cur' (Z.min cur' len') (wz (A' + esp)) elw err' hack 4 6 clen csz esp cur
                  PC40 MU5 WM5 MI5 ltac:(repeat apply Forall_cons; try apply Forall_nil; unfold wcls; cbn; lia)
                  ltac:(repeat apply Forall_cons; try apply Forall_nil; cbn; lia) ltac:(repeat apply Forall_cons; try apply Forall_nil; rewrite ERRNOV; cbn; lia)
                  ltac:(left; repeat apply Forall_cons; try apply Forall_nil; cbn; lia)
                  SC5 ENT5 (conj CTL5 CTLB)) as PC5.
    eapply pe_exitC; [exact PC5| lia| lia| lia].
  Qed.

  #[using="Type"] Lemma CONT_mono : forall M M' gp F fc, CONT M' gp F fc -> (M <= M')%Z -> CONT M gp F fc.
  Proof. intros M M' gp F fc HC LE. unfold CONT in *. intros. eapply HC; [eassumption| lia]. Qed.

  #[using="GMX"] Lemma pe_meas_nonneg : forall entp cur esp csz elw, ent_ok entp cur esp csz elw -> (0 <= pe_meas entp elw)%Z.
  Proof.
    intros entp cur esp csz elw (E1 & E2 & E3). unfold pe_meas.
    destruct (Z.eqb_spec entp 1); [lia|]. destruct (Z.eqb_spec entp 3).
    { destruct (E2 ltac:(lia)) as (elen & -> & R). unfold elen_of. rewrite unsigned_lit by lia. lia. }
    destruct (Z.eqb_spec entp 5); [| lia]. destruct (E2 ltac:(lia)) as (elen & -> & R). unfold elen_of. rewrite unsigned_lit by lia. lia.
  Qed.

  #[using="AC LOK REALLOCPC TPV ERRNOV CAN ERRNC BLK4096 BLKIMG GERM GMST IWST TABA ZEROA PHS_munch PHS_hp TABST ZST QLO QLO2 STK0 LO0 CEIL QP PB BHI GMX P8 Q8 HCALL"] Lemma pe_loop : forall (n : nat) gp F fc s LB m cur A len cap km bs ebw elw err hack pos entp clen csz esp ns hs X meth
      t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 t3 t4 t5 t6 x1,
    PI s LB m cur A len cap (Some km) bs ebw elw err hack pos entp clen csz esp ns hs X meth -> (pe_meas entp elw < Z.of_nat n)%Z ->
    SREACH AI (pent_post gp F fc) (PRS 0x157b0 x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (wz S) s7 t3 t4 t5 t6 gp F fc m) s LB.
  Proof.
    induction n as [|n IH]; intros until x1; intros INV HM.
    { exfalso. pose proof INV as INV'. open_PI INV'. pose proof (pe_meas_nonneg _ _ _ _ _ EOK). lia. }
    assert (HC : CONT (pe_meas entp elw) gp F fc).
    { unfold CONT. intros. eapply IH; [eassumption| lia]. }
    pose proof INV as INV'. open_PI INV'. destruct PCTL as [CTL CTLB].
    destruct (msg_facts _ _ _ _ _ _ _ _ HR PMSG) as (_ & _ & _ & _ & OKSL & _). destruct (OKSL km eq_refl) as (_ & _ & APOS & _). clear OKSL.
    eapply sreach_evt. { rewrite TPV. eapply (pe_dispatch P q err hack pos entp clen csz esp); unfold ctl9; [exact MI| exact CTL| lia]. }
    intros ms' [a0' ->]. rewrite <- TPV. unfold pe_target.
    assert (CASES : (entp = 0 \/ entp = 1 \/ entp = 2 \/ entp = 3 \/ entp = 4 \/ entp = 5 \/ entp = 6)%Z) by lia.
    try clear HR; try clear HE; try clear MI; try clear ST; try clear ERR; try clear FSH; try clear FX; try clear PSC; try clear PMSG; try clear PENT; try clear CTL; try clear CTLB; try clear PHL; try clear XV; try clear PMETH; try clear PVER; try clear PRS_; try clear BSUB; try clear ND; try clear GM; try clear IW; try clear HPX; try clear PH; try clear errv; try clear CUR; try clear EOK.
    destruct CASES as [->|[->|[->|[->|[->|[->| ->]]]]]]; cbn [Z.eqb Pos.eqb].
    - eapply pe_case_default; exact INV.
    - eapply pe_case1; [exact HC| exact INV| reflexivity| reflexivity].
    - eapply pe_case2; [exact INV| reflexivity| lia].
    - eapply pe_case3; [exact HC| exact INV| reflexivity| reflexivity].
    - eapply pe_case4; [exact INV| reflexivity| lia].
    - eapply pe_case5; [exact HC| exact INV| reflexivity| reflexivity].
    - eapply pe_case6; [exact INV| reflexivity].
  Qed.

  #[using="AC LOK REALLOCPC TPV ERRNOV CAN ERRNC BLK4096 BLKIMG GERM GMST IWST TABA ZEROA PHS_munch PHS_hp TABST ZST QLO QLO2 STK0 LO0 CEIL QP PB BHI GMX P8 Q8 HCALL"] Theorem parser_parse_entity_B : forall gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (F : bvmap 5 word) fc s LB
      (cur A len cap : Z) (km : K) (bs : list byte) (ebw elw : word) (err hack pos entp clen csz esp X meth : Z) (ns : list (BLK * Z)) (hs : list hdr) (errv : word),
    RHEAP rsegs AI s LB m0 -> RENV rsegs AI m0 B -> mem_inv rsegs m0 -> stk rsegs m0 lo (q + 144) ->
    rw_cells rsegs m0 (al_errno L_) [C4 errv] ->
    p_scan m0 P cur -> p_msg AI m0 LB P A len cap (Some km) bs -> (0 <= cur <= len)%Z ->
    p_ent m0 P ebw elw -> p_ctl m0 P err hack pos entp clen csz esp -> p_hlist AI m0 P ns hs X -> (X + 2 * (len - cur) <= VMAX)%Z ->
    p_meth m0 P meth -> p_ver m0 P isreq maj min -> p_rs m0 P rm sc ->
    bsub AI (hl_blocks AI ns hs ++ okb AI (Some km) A cap ++ LBK) LB -> NoDup (map blk_id (hl_blocks AI ns hs ++ okb AI (Some km) A cap ++ LBK)) ->
    rw_cells rsegs m0 GMAXA [C8 (wz gmax)] -> rw_cells rsegs m0 INITWASCALLED [C1 (Z_to_bv 8 0)] -> bytes_at rsegs m0 GOT_GMAX (le8 (wz GMAXA)) -> PHS m0 ->
    ent_ok entp cur esp csz elw ->
    SREACH AI (pent_post gp F fc)
      (MS (mkR ra (wz (q + 144)) gp (wz (al_tp L_)) t0 t1 t2 s0e s1e (wz P) a1 a2 a3 a4 a5 a6 a7 s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e t3 t4 t5 t6)
          F (wz parse_entity_entry) fc None m0 (seg_rom rsegs)) s LB.
  Proof.
    intros until errv. intros HR HE MI ST ERR PSC PMSG CUR PENT PCTL PHL XV PMETH PVER PRS_ BSUB ND GM IW GG PH EOK.
    pose proof alloc_ceiling_bounds as CE. pose proof alloc_ceiling_aligned8 as CE8.
    destruct (proj1 (bsub_app AI _ _ _) BSUB) as [SUBH BSUB2]. destruct (proj1 (bsub_app AI _ _ _) BSUB2) as [SUBM SUBK].
    eapply sreach_evt. { rewrite TPV. eapply (pe_entry P q lo QLO1 LO0 QP PHI63); [exact P8| exact ST| exact MI| exact GG]. }
    intros ms1 (m1 & a0' & a1' & a2' & a3' & a4' & a5' & -> & MU1 & WM1 & MI1 & ST1 & FX1 & FSH1). rewrite <- TPV.

    assert (HR1 : RHEAP rsegs AI s LB m1).
    { eapply (ai_heap_frame rsegs AI); [exact HR| exact MU1| exact WM1|]. constructor; [left; cbn; lia| constructor]. }
    assert (HE1 : RENV rsegs AI m1 B).
    { eapply (ai_env_frame rsegs AI); [exact HR| exact HE| exact MU1| exact WM1|]. constructor; [left; cbn; lia| constructor]. }
    assert (HP1 : hpx AI WE LBK (q + 144) m0 m1).
    { eapply (hpx_seg rsegs AI); [exact LOK| exact HR| exact SUBK| exact MU1| exact WM1|]. constructor; [left; cbn; lia| constructor]. }
    assert (SUBHM : forall b, In b (hl_blocks AI ns hs ++ okb AI (Some km) A cap) -> In b LB).
    { intros b Hb. apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [exact (SUBH b Hb)| exact (SUBM b Hb)]. }
    pose proof (seg_heap_pres s LB m0 _ _ m0 m1 HR SUBHM MU1 WM1 ltac:(constructor; [cbn; lia| constructor])) as HPh.
    assert (TR : forall X0 cs, rw_cells rsegs m0 X0 cs -> (X0 + Z.of_nat (cells_size cs) <= q \/ q + 144 <= X0)%Z -> rw_cells rsegs m1 X0 cs).
    { intros X0 cs H H1. eapply rw_cells_transport; [exact H| exact MU1| exact WM1| cbn; lia]. }
    destruct (lo_errno_img rsegs AI LOK) as (we & Hwe & WE1 & WE2). pose proof (lo_img_ceiling rsegs AI LOK we Hwe) as WE3.
    assert (INV1 : PI s LB m1 cur A len cap (Some km) bs ebw elw err hack pos entp clen csz esp ns hs X meth).
    { split; [exact HR1|]. split; [exact HE1|]. split; [exact MI1|]. split; [exact ST1|]. split; [eexists; apply (TR _ _ ERR); cbn; lia|].
      split; [exact FSH1|]. split; [exact FX1|]. split; [apply (TR _ _ PSC); cbn; lia|].
      split. { eapply pe_msg_pres; [exact PMSG| exact MU1| exact WM1| cbn; lia| exact HPh| | intros b Hb; exact (SUBM b Hb)].
               intros b Hb. apply in_or_app. right. exact Hb. }
      split; [exact CUR|]. split; [apply (TR _ _ PENT); cbn; lia|].
      split; [destruct PCTL as [CTL CTLB]; split; [apply (TR _ _ CTL); cbn; lia| exact CTLB]|].
      split. { eapply pe_hlist_pres; [exact PHL| exact MU1| exact WM1| cbn; lia| exact HPh|]. intros b Hb. apply in_or_app. left. exact Hb. }
      split; [exact XV|]. split; [destruct PMETH as [MC MR]; split; [apply (TR _ _ MC); cbn; lia| exact MR]|].
      split; [destruct PVER as ([pad VC] & VR); split; [eexists; apply (TR _ _ VC); cbn; lia| exact VR]|].
      split; [destruct PRS_ as [RC RR]; split; [apply (TR _ _ RC); cbn; lia| exact RR]|].
      split; [exact BSUB|]. split; [exact ND|]. split; [apply (TR _ _ GM); cbn; lia|]. split; [apply (TR _ _ IW); cbn; lia|].
      split; [exact HP1|]. split; [| exact EOK].
      destruct TABST as (tlo & thi & THst & T1 & T2). destruct ZST as (zlo & zhi & ZHst & Z1 & Z2).
      destruct (lo_static_img rsegs AI LOK tlo thi THst) as (tw & Htw & TW1 & TW2). pose proof (lo_img_ceiling rsegs AI LOK tw Htw).
      destruct (lo_static_img rsegs AI LOK zlo zhi ZHst) as (zw & Hzw & ZW1 & ZW2). pose proof (lo_img_ceiling rsegs AI LOK zw Hzw).
      eapply PHS_munch; [exact MU1| exact WM1| cbn; lia| cbn; lia| exact PH]. }
    eapply (pe_loop (Datatypes.S (Z.to_nat (pe_meas entp elw)))); [exact INV1|].
    pose proof (pe_meas_nonneg _ _ _ _ _ EOK). lia.
  Qed.
End W.
