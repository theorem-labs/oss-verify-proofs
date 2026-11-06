From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YM05 YL0i YL01.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import Contract KindBGlue Img0 FrameAPI.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Mem Frame.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjRoundTrip.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import PjStruct.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import ReaderRes tx_put_c TxCalls TxRet.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import WriterSpec WriterValue WriterApp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import WriterRet PjWriteHyp round_trip_text_c RttDefs strcmp_c strlen_c same_c memcpy_c pj_free_c fuzz_free_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require parse_noting_c fuzz_alloc_ran_out_c strtod_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import RttGlue.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import RttModel.
Import ListNotations.
Local Open Scope Z_scope.

(* round_trip_text of the #102 ubsan twin 27566683 (round_trip_text_c.v, 0x15334, 388 bytes): the plain build's
   instructions (lib/Prog/RttBase.v) at plain pc + 0x5ac, other immediates.  Frame `addi sp, sp, -0x70`; ra s0 s1 s2 s3 s4
   s5 saved at S - 8 .. S - 56 (S the entry sp), the 56-byte save area [S - 56, S); locals [S - 112, S - 56): the struct
   text record (32 bytes: b, n, cap, failed) at S - 112, and the read-back's struct pj `back` (56 bytes) at S - 112 after
   the record is dead.  Registers: s0 = copy, s1 = doc, s2 = text, s3 = pretty and then want, s4 = parse_noting's rc,
   s5 = the page pointer 0x353d0 of the two flag loads (auipc s5, 0x20 at 0x153d0; lbu -0x180(s5) = GL_OWN_RAN_OUT).
   Stage pcs (each the pc after a call's return or a branch): 0x15364 pj_write returned; 0x1538c tx_put ""; 0x153a0
   tx_value; 0x153b8 rendered done (tx_put "\n" when pretty); 0x153e4 the ran-out arm (a flag is nonzero); 0x1544c
   parse_noting returned; 0x15460 free (want) and fuzz_free (text) returned; 0x15488 same returned nonzero (the copy
   branch). *)

Section P.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Variable F : ResForm.
Let segs := ms_segs B.
Let MR := aa_MR API.
Hypothesis HSEG : ms_segs B = rsegs.
Hypothesis FA : forall fx' : YK11.FPState, @frame_allocator rc fx' B API.

Lemma rtt_AX : AllocExtra B (aa_MR API).
Proof using fx HSEG FA. destruct (FA fx) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.

Lemma rtt_FG : forall L A mem md a, aa_MR API L A mem md -> in_globals frame_G a -> ~ owned B L A a.
Proof using fx HSEG FA. destruct (FA fx) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.

Lemma rtt_img_low : KindBGlue.img_low B.
Proof using fx HSEG FA.
  apply (KindBGlue.img_low_of_check B CEIL_MIN); [unfold KindBGlue.img_check; rewrite HSEG; vm_compute; reflexivity |].
  pose proof alloc_ceiling_val. lia.
Qed.

Definition rtt_ent (L0 : layout) (A0 : astate) (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model)
    (Lam0 : list (Z * Z)) (peak0 cnt0 : Z) (b0 : rf_R F) (doc pretty copy : Z) (t : jv) (D : list (Z * Z)) : Prop :=
  let p := negb (pretty =? 0) in
  reader_env B API RTT_K L0 A0 regs0 mem0 md0 /\
  st_init_done A0 = true /\
  ledger B L0 A0 mem0 Lam0 peak0 cnt0 (2 ^ 64 - 1) /\ cnt0 < 2 ^ 62 /\
  rf_ok F A0 b0 /\
  getr regs0 10 = Z_to_bv 64 doc /\ getr regs0 11 = Z_to_bv 64 pretty /\ getr regs0 12 = Z_to_bv 64 copy /\
  (pretty = 0 \/ pretty = 1) /\
  pj_node segs mem0 (lin Lam0) doc t D /\ (forall bk, In bk D -> In bk Lam0) /\
  doc <> 0 /\ spZ regs0 <= doc /\
  PjRoundTrip.pj_wf jr_strtod t /\ (depth t <= 32)%nat /\ wlen t p + 1 <= 2 ^ 28 /\
  (copy = 0 \/ copy <> 0 /\ pj_rw segs mem0 copy /\ spZ regs0 <= copy /\ (copy + 56 <= doc \/ doc + 56 <= copy)) /\
  rtt_rooms F b0 cnt0 t p.

(* the entry bytes of g_ran_out and g_own_ran_out (round_trip_text_c.v's ro / oo premises) *)
Definition rtt_fl (mem : word -> option byte) (ro oo : Z) : Prop :=
  0 <= ro < 256 /\ 0 <= oo < 256 /\
  Mem.bytes_at segs mem fuzz_alloc_ran_out_c.G_RAN_OUT (Mem.le1 (Z_to_bv 64 ro)) /\
  Mem.bytes_at segs mem GL_OWN_RAN_OUT (Mem.le1 (Z_to_bv 64 oo)).

Definition rtt_post (L0 : layout) (A0 : astate) (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model)
    (Lam0 : list (Z * Z)) (peak0 cnt0 : Z) (b0 : rf_R F) (doc pretty copy : Z) (t : jv) (D : list (Z * Z))
    (ro oo : Z) (c' : config) : Prop :=
  let p := negb (pretty =? 0) in
  exists (fx' : YK11.FPState) L' A' regs' mem' md' (Lam' : list (Z * Z)) (peak' : Z),
    c' = mkCfg (@mkst fx' regs' (getr regs0 1) mem' (seg_rom segs)) md' /\
    frm_zero (@fp_csr fx') /\ fregs_kept fx fx' /\
    rtt_rel B API RTT_K regs0 (rtt_writes copy) L0 A0 mem0 md0 L' A' regs' mem' md' /\
    rd_cells B mem' /\
    Mem.bytes_at segs mem' fuzz_alloc_ran_out_c.G_RAN_OUT (Mem.le1 (Z_to_bv 64 ro)) /\
    Mem.bytes_at segs mem' GL_OWN_RAN_OUT (Mem.le1 (Z_to_bv 64 oo)) /\
    ((ro <> 0 \/ oo <> 0) /\ getr regs' 10 = Z_to_bv 64 1 /\
       ledger B L' A' mem' Lam' peak' (cnt0 + wcalls t p) (2 ^ 64 - 1) /\
       peak0 <= peak' /\
       pj_node segs mem' (lin Lam') doc t D /\
       Permutation Lam' Lam0 /\
       rf_ok F A' (rtt_bo F b0 cnt0 t p) /\
       (copy <> 0 -> forall i, 0 <= i < 56 -> mbyte segs mem' (copy + i) = mbyte segs mem0 (copy + i))
     \/
     ro = 0 /\ oo = 0 /\ getr regs' 10 = Z_to_bv 64 0 /\
       ledger B L' A' mem' Lam' peak' (cnt0 + wcalls t p + Z.of_nat (PjRoundTrip.tcalls t)) (2 ^ 64 - 1) /\
       peak0 <= peak' /\
       pj_node segs mem' (lin Lam') doc t D /\
       (copy = 0 -> Permutation Lam' Lam0 /\
         exists Db Df, Permutation Db Df /\
           Permutation (map snd Db) (map Z.of_nat (lsz (PjRoundTrip.ttrace t))) /\
           Z.of_nat (length Db) = nlive (PjRoundTrip.ttrace t) /\
           rf_ok F A' (rf_frees F (rtt_bf F b0 cnt0 t p) Df)) /\
       (copy <> 0 -> rf_ok F A' (rtt_bf F b0 cnt0 t p) /\
          exists Db, Permutation Lam' (Db ++ Lam0) /\ new_blks L0 A0 Db /\ pj_node segs mem' (lin Lam') copy t Db /\
            Permutation (map snd Db) (map Z.of_nat (lsz (PjRoundTrip.ttrace t))) /\
            Z.of_nat (length Db) = nlive (PjRoundTrip.ttrace t))).

(* The walk's frame relation runs with the write set rtt_writes 0 (= alloc_statics): nothing before the final memcpy
   writes *copy, which the ran-out arm's post states.  The memcpy stage widens it to rtt_writes copy. *)
Definition rtt_inv (L0 : layout) (A0 : astate) (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model)
    (Lam0 : list (Z * Z)) (peak0 : Z) (doc copy : Z) (t : jv) (D : list (Z * Z))
    (fx' : YK11.FPState) (L : layout) (A : astate) (mem : word -> option byte) (md : Model)
    (X Lam : list (Z * Z)) (peak cnt : Z) (bnd : rf_R F) : Prop :=
  let S := spZ regs0 in
  rstep B API RTT_K S (rtt_writes 0) (fun _ => False) L0 A0 mem0 md0 L A mem md /\
  (forall a k, In (a, k) (blocks L0 A0) -> k <= 0 -> In (a, k) (blocks L A)) /\
  st_init_done A = true /\ rd_cells B mem /\
  frm_zero (@fp_csr fx') /\ fregs_kept fx fx' /\
  ledger B L A mem Lam peak cnt (2 ^ 64 - 1) /\ peak0 <= peak /\
  Permutation Lam (X ++ Lam0) /\
  pj_node segs mem (lin Lam) doc t D /\
  rf_ok F A bnd /\
  (copy <> 0 -> pj_rw segs mem copy) /\
  Mem.bytes_at segs mem (S - 8) (Mem.le8 (getr regs0 1)) /\ Mem.bytes_at segs mem (S - 16) (Mem.le8 (getr regs0 8)) /\
  Mem.bytes_at segs mem (S - 24) (Mem.le8 (getr regs0 9)) /\ Mem.bytes_at segs mem (S - 32) (Mem.le8 (getr regs0 18)) /\
  Mem.bytes_at segs mem (S - 40) (Mem.le8 (getr regs0 19)) /\ Mem.bytes_at segs mem (S - 48) (Mem.le8 (getr regs0 20)) /\
  Mem.bytes_at segs mem (S - 56) (Mem.le8 (getr regs0 21)) /\ Mem.wr_at segs mem (S - 56) 56.

(* sp = S - 112, s0 = copy, s1 = doc; s2 .. s5 as the stage says; gp, tp, s6 .. s11 the entry's *)
Definition rtt_regs (regs0 regs : bvmap 5 word) (copy : Z) (s2v s3v s4v s5v : word) : Prop :=
  getr regs 2 = Z_to_bv 64 (spZ regs0 - 112) /\ getr regs 8 = Z_to_bv 64 copy /\ getr regs 9 = getr regs0 10 /\
  getr regs 18 = s2v /\ getr regs 19 = s3v /\ getr regs 20 = s4v /\ getr regs 21 = s5v /\
  getr regs 3 = getr regs0 3 /\ getr regs 4 = getr regs0 4 /\
  (forall r, 22 <= r <= 27 -> getr regs (Z_to_bv 5 r) = getr regs0 (Z_to_bv 5 r)).

Definition rt_text (L0 : layout) (A0 : astate) (mem : word -> option byte) (Lam : list (Z * Z)) (t : jv) (p : bool)
    (q : Z) : Prop :=
  0 < q /\ In (q, wcap t p) Lam /\
  (forall a k, In (a, k) (blocks L0 A0) -> 0 < k -> a <> q - 16) /\
  Forall (fun c => 0 < c < 256) (wdoc t p) /\
  Mem.bytes_at segs mem q (map (Z_to_bv 8) (wdoc t p ++ [0])).

Definition rt_harn (L0 : layout) (A0 : astate) (L : layout) (A : astate) (mem : word -> option byte)
    (Lam : list (Z * Z)) (r want len cap : Z) (txt : list byte) : Prop :=
  0 <= want < 2 ^ 64 /\ 0 <= len < 2 ^ 64 /\ 0 <= cap < 2 ^ 64 /\
  text_rec B mem r want len cap /\ (forall i, 0 <= i < 24 -> writable_at segs mem (r + i)) /\
  tx_inv B L A mem want len cap txt /\
  (forall a k, In (a, k) (blocks L0 A0) -> 0 < k -> a <> want) /\
  (forall a n, In (a, n) Lam -> a - 16 <> want).

Lemma run_N : forall (fx1 : YK11.FPState) regs pc mem md (Q : machine_state -> Prop) (P : config -> Prop),
  ms_segs B = rsegs -> m_halted md = None -> m_vm_lazy md = [] -> ro_agree (ms_segs B) mem ->
  Exec.evt (ms_segs B) Q
    (MState.MS (rmk regs) (@fp_regs fx1) pc (@fp_csr fx1) None (normalize (ms_segs B) mem) (seg_rom (ms_segs B))) ->
  (forall ms, Q ms -> exists R pc' m0, ms = MState.MS R (@fp_regs fx1) pc' (@fp_csr fx1) None m0 (seg_rom (ms_segs B))) ->
  (forall R pc' m0 mem' regs', Q (MState.MS R (@fp_regs fx1) pc' (@fp_csr fx1) None m0 (seg_rom (ms_segs B))) ->
     mem_rel (ms_segs B) mem' m0 -> ro_same (ms_segs B) mem mem' -> (forall r, getr regs' r = getr R r) ->
     SR (ms_segs B) (mkCfg (@mkst fx1 regs' pc' mem' (seg_rom (ms_segs B))) md) P) ->
  SR (ms_segs B) (mkCfg (@mkst fx1 regs pc mem (seg_rom (ms_segs B))) md) P.
Proof.
  intros fx1 regs pc mem md Q P HS Hh Hl RA HE HQ HK.
  assert (WX : wx_apart (ms_segs B) = true) by (rewrite HS; exact wx_apart_rsegs).
  pose proof (evt_normalize (ms_segs B) Q (rmk regs) (@fp_regs fx1) pc (@fp_csr fx1) None mem (seg_rom (ms_segs B))
    WX RA HE) as HN.
  eapply (evt_SR_canon (ms_segs B) (@mkst fx1 regs pc mem (seg_rom (ms_segs B))) _ md P);
    [exact HN | exact Hh | exact Hl |].
  intros ms' (can & (s0 & HQ0 & HR & HO) & Heq).
  destruct (HQ s0 HQ0) as (R & pc' & m0 & ->).
  destruct can as [cr cf cpc csv crs cfc cm cro].
  destruct HR as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8). cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr
    ms_rom ms_mem MState.MS] in R1, R2, R3, R4, R5, R6, R7, R8, HO.
  destruct Heq as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8).
  destruct ms' as [regs' fr' pcv' svc' rv' fc' m' ro'].
  cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_mem] in E1, E2, E3, E4, E5, E6, E7, E8.
  subst. eapply HK; [eassumption | eassumption | eassumption | apply kb_getr_eqv; eassumption].
Qed.

Lemma fregs_kept_trans : forall f1 f2 f3 : YK11.FPState, fregs_kept f1 f2 -> fregs_kept f2 f3 -> fregs_kept f1 f3.
Proof. intros f1 f2 f3 H1 H2 r Hr. rewrite (H2 r Hr). exact (H1 r Hr). Qed.

Lemma ia_bytes : forall m m' x bs, Mem.bytes_at segs m x bs ->
  (forall i, 0 <= i < Z.of_nat (length bs) -> mbyte segs m' (x + i) = mbyte segs m (x + i)) ->
  Mem.bytes_at segs m' x bs.
Proof.
  intros m m' x bs (H1 & H2 & H3) HE. split; [exact H1|]. split; [exact H2|]. intros i Hi.
  rewrite <- (H3 i Hi). exact (HE (Z.of_nat i) ltac:(lia)).
Qed.

Lemma ia_wr : forall m m' x n, Mem.wr_at segs m x n ->
  (forall i, 0 <= i < n -> (writable_at segs m (x + i) <-> writable_at segs m' (x + i))) ->
  Mem.wr_at segs m' x n.
Proof.
  intros m m' x n (H1 & H2 & H3) HE. split; [exact H1|]. split; [exact H2|]. intros i Hi.
  exact (proj1 (HE i Hi) (H3 i Hi)).
Qed.

Lemma ia_stk : forall m m' lo hi, Frame.stk segs m lo hi ->
  (forall a, lo <= a < hi -> mbyte segs m' a = mbyte segs m a /\ (writable_at segs m a <-> writable_at segs m' a)) ->
  Frame.stk segs m' lo hi.
Proof.
  intros m m' lo hi (H1 & H2 & H3) HE. split; [exact H1|]. split; [exact H2|]. intros a Ha.
  destruct (H3 a Ha) as [W [b Hb]]. destruct (HE a Ha) as [E1 E2].
  split; [exact (proj1 E2 W)|]. exists b.
  change (mbyte segs m' a = Some b). rewrite E1. exact Hb.
Qed.

Lemma inv_after : forall L0 A0 regs0 mem0 md0 Lam0 peak0 cnt0 b0 doc pretty copy t D
    fx1 L A mem md X Lam peak cnt bnd Kc Ec gc fx2 L' A' mem' md' X' Lam' peak' cnt' bnd',
  rtt_ent L0 A0 regs0 mem0 md0 Lam0 peak0 cnt0 b0 doc pretty copy t D ->
  rtt_inv L0 A0 regs0 mem0 md0 Lam0 peak0 doc copy t D fx1 L A mem md X Lam peak cnt bnd ->
  rstep B API Kc (spZ regs0 - 112) Ec gc L A mem md L' A' mem' md' ->
  0 <= Kc -> 112 + Kc <= RTT_K ->
  (forall a, Ec a -> alloc_statics a \/ (spZ regs0 - 112 <= a < spZ regs0 - 56) \/
     (0 <= a < alloc_ceiling /\ ~ in_img B a /\ forall b k, In (b, k) (blocks L A) -> ~ gc b -> ~ (b <= a < b + k))) ->
  (forall a, spZ regs0 - 112 <= a < spZ regs0 - 56 -> Ec a -> writable_at segs mem' a) ->
  (forall a k, In (a, k) (blocks L0 A0) -> 0 < k -> ~ gc a) ->
  (forall a k, In (a, k) (blocks L A) -> k <= 0 -> In (a, k) (blocks L' A')) ->
  ro_agree segs mem' ->
  frm_zero (@fp_csr fx2) -> fregs_kept fx1 fx2 ->
  ledger B L' A' mem' Lam' peak' cnt' (2 ^ 64 - 1) -> peak <= peak' -> Permutation Lam' (X' ++ Lam0) ->
  pj_node segs mem' (lin Lam') doc t D ->
  rf_ok F A' bnd' ->
  rtt_inv L0 A0 regs0 mem0 md0 Lam0 peak0 doc copy t D fx2 L' A' mem' md' X' Lam' peak' cnt' bnd'.
Proof using fx HSEG FA.
  intros L0 A0 regs0 mem0 md0 Lam0 peak0 cnt0 b0 doc pretty copy t D fx1 L A mem md X Lam peak cnt bnd
    Kc Ec gc fx2 L' A' mem' md' X' Lam' peak' cnt' bnd'
    ENT INV STEP HK0 HK1 HEC HECW HG HZ RA' FRM' FRG' LED' PK' PERM' NODE' RES'.
  pose proof ENT as (REN & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & DOCS & _ & _ & _ & COPY & _).
  pose proof REN as (SEGB & TPB & ERRB & GOTB & GUARDB & PRE0 & SP47 & GT & FRM0 & RD0).
  pose proof PRE0 as (MR0 & WF0 & BD0 & RA0 & SP16 & SPC & SP63 & WIN0 & TP0 & ERRW0 & AUX0).
  destruct INV as (RS & Z0 & INIT & RD & FRM & FREG & LED & PK & PERM & NODE & RES & CP &
                   SL8 & SL16 & SL24 & SL32 & SL40 & SL48 & SL56 & WR56).
  pose proof RS as (MRc & WFc & BDc & INc & PSc & MDc & ACc & IMc & BKc & WRc).
  pose proof STEP as (MR' & WF' & BD' & IN' & PS' & MD' & AC' & IM' & BK' & WR').
  pose proof rtt_img_low as (HIL & _).
  pose proof alloc_ceiling_val as HCV.
  set (S := spZ regs0) in *.
  assert (HRK : 112 <= RTT_K) by lia.
  assert (HERR : forall a, errno_addr B <= a < errno_addr B + 4 -> a < alloc_ceiling).
  { intros a Ha. pose proof (errno_img B API HSEG rtt_AX rtt_FG ERRB (a - errno_addr B) ltac:(lia)) as Hi.
    replace (errno_addr B + (a - errno_addr B)) with a in Hi by lia. apply HIL in Hi. lia. }
  assert (HST : forall a, alloc_statics a -> a < alloc_ceiling).
  { intros a Ha. destruct (statics_img B API HSEG rtt_AX rtt_FG a Ha) as [Hi _]. apply HIL in Hi. lia. }
  assert (STW : rstep B API RTT_K S Ec gc L A mem md L' A' mem' md').
  { apply (rstep_widen B API HSEG rtt_AX rtt_FG Kc (S - 112) RTT_K S Ec gc L A mem md L' A' mem' md' STEP);
      [lia | lia | lia | lia | exact WRc |].
    intros a Ha Hn He. destruct (HEC a He) as [Hs | [Hw | (Hlo & _ & _)]].
    - pose proof (HST a Hs). lia.
    - apply HECW; [lia | exact He].
    - lia. }
  assert (STD : rstep B API RTT_K S (rtt_writes 0) gc L A mem md L' A' mem' md').
  { apply (rstep_E_drop B API HSEG rtt_AX rtt_FG RTT_K S Ec (rtt_writes 0) gc L A mem md L' A' mem' md' STW MRc);
      [lia | exact ERRB |].
    intros a He. destruct (HEC a He) as [Hs | [Hw | Hb]].
    - left. right. exact Hs.
    - right. left. unfold rwin. left. lia.
    - right. right. exact Hb. }
  assert (STQ : rstep B API RTT_K S (rtt_writes 0) (fun _ => False) L0 A0 mem0 md0 L' A' mem' md').
  { eapply (rstep_E B API HSEG rtt_AX rtt_FG).
    - eapply (rstep_seq B API HSEG rtt_AX rtt_FG); [exact RS | exact STD |].
      intros a k Hin Hk _. exact (HG a k Hin Hk).
    - intros a [H|H]; exact H.
    - intros a H; exact H. }
  assert (KEEP : forall a, S - 56 <= a < 2 ^ 64 ->
      mbyte segs mem' a = mbyte segs mem a /\ (writable_at segs mem a <-> writable_at segs mem' a)).
  { intros a Ha. apply AC'; [lia | |].
    - unfold rwin. intros [Hr|Hr]; [lia | pose proof (HERR a Hr); lia].
    - intros He. destruct (HEC a He) as [Hs | [Hw | (Hlo & _ & _)]]; [pose proof (HST a Hs) | |]; lia. }
  assert (HCP : copy <> 0 -> S <= copy /\ copy + 56 <= 2 ^ 64).
  { intros Hc. destruct COPY as [C0|(_ & (_ & _ & Hhi & _) & Hs & _)]; [contradiction|]. split; [exact Hs | exact Hhi]. }
  unfold rtt_inv. fold S.
  split; [exact STQ|].
  split; [intros a k Hin Hk; apply HZ; [apply Z0; assumption | exact Hk]|].
  split; [apply IN'; exact INIT|].
  split; [exact (rd_cells_of_MR B API HSEG rtt_AX rtt_FG L' A' mem' md' MR' RA')|].
  split; [exact FRM'|].
  split; [exact (fregs_kept_trans fx fx1 fx2 FREG FRG')|].
  split; [exact LED'|].
  split; [lia|].
  split; [exact PERM'|].
  split; [exact NODE'|].
  split; [exact RES'|].
  split.
  { intros Hc. destruct (CP Hc) as [Hal Hstk]. destruct (HCP Hc) as [Hs Hhi]. split; [exact Hal|].
    apply (ia_stk mem); [exact Hstk|]. intros a Ha. apply KEEP. lia. }
  assert (HB : forall x bs, S - 56 <= x -> x + Z.of_nat (length bs) <= S -> Mem.bytes_at segs mem x bs ->
      Mem.bytes_at segs mem' x bs).
  { intros x bs H1 H2 Hb. apply (ia_bytes mem); [exact Hb|]. intros i Hi. apply KEEP. lia. }
  split; [apply HB; [lia | rewrite Mem.length_le8; lia | exact SL8]|].
  split; [apply HB; [lia | rewrite Mem.length_le8; lia | exact SL16]|].
  split; [apply HB; [lia | rewrite Mem.length_le8; lia | exact SL24]|].
  split; [apply HB; [lia | rewrite Mem.length_le8; lia | exact SL32]|].
  split; [apply HB; [lia | rewrite Mem.length_le8; lia | exact SL40]|].
  split; [apply HB; [lia | rewrite Mem.length_le8; lia | exact SL48]|].
  split; [apply HB; [lia | rewrite Mem.length_le8; lia | exact SL56]|].
  apply (ia_wr mem); [exact WR56|]. intros i Hi. apply KEEP. lia.
Qed.


(* g_ran_out (fuzz_alloc_ran_out_c.G_RAN_OUT = GL_RAN_OUT) and g_own_ran_out (GL_OWN_RAN_OUT): image bytes inside the
   second run of FrameAPI.frame_G = LedgerCells.GL_runs, never owned, and not ledger words *)
Lemma rtt_flag_img : forall a,
  (fuzz_alloc_ran_out_c.G_RAN_OUT <= a < fuzz_alloc_ran_out_c.G_RAN_OUT + 1 \/ GL_OWN_RAN_OUT <= a < GL_OWN_RAN_OUT + 1) ->
  in_img B a /\ never_owned B API a /\ ~ alloc_statics a.
Proof using fx HSEG FA.
  intros a Ha.
  assert (Ha' : GL_OWN_RAN_OUT <= a < GL_OWN_RAN_OUT + 16)
    by (unfold fuzz_alloc_ran_out_c.G_RAN_OUT, GL_RAN_OUT, GL_OWN_RAN_OUT in *; lia).
  split; [|split].
  - apply (rg_img_range B API HSEG rtt_AX rtt_FG GL_OWN_RAN_OUT (GL_OWN_RAN_OUT + 16));
      [vm_compute; reflexivity | exact Ha'].
  - unfold never_owned. intros L0 A0 mem0 md0 HM. apply (rtt_FG L0 A0 mem0 md0 a HM).
    unfold in_globals, frame_G, GL_runs. exists GL_OWN_RAN_OUT, 40. split; [right; left; reflexivity | lia].
  - unfold alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL, GL_LIVE, GL_PEAK, GL_COUNT, GL_FAIL, GL_OWN_RAN_OUT in *. lia.
Qed.

(* the two flag bytes at any stage are their entry bytes: nothing in the walk writes them *)
Lemma rtt_fl_inv : forall L0 A0 regs0 mem0 md0 Lam0 peak0 cnt0 b0 doc pretty copy t D ro oo
    fx1 L A mem md X Lam peak cnt bnd,
  rtt_ent L0 A0 regs0 mem0 md0 Lam0 peak0 cnt0 b0 doc pretty copy t D ->
  rtt_inv L0 A0 regs0 mem0 md0 Lam0 peak0 doc copy t D fx1 L A mem md X Lam peak cnt bnd ->
  rtt_fl mem0 ro oo -> rtt_fl mem ro oo.
Proof using fx HSEG FA.
  intros L0 A0 regs0 mem0 md0 Lam0 peak0 cnt0 b0 doc pretty copy t D ro oo fx1 L A mem md X Lam peak cnt bnd
    ENT INV (R1 & R2 & B1 & B2).
  pose proof ENT as (REN & _).
  pose proof REN as (SEGB & TPB & ERRB & GOTB & GUARDB & PRE0 & SP47 & GT & FRM0 & RD0).
  pose proof PRE0 as (MR0 & WF0 & BD0 & RA0 & SP16 & SPC & SP63 & WIN0 & TP0 & ERRW0 & AUX0).
  destruct INV as (RS & _).
  pose proof RS as (_ & _ & _ & _ & _ & _ & _ & IMc & _).
  pose proof rtt_img_low as (HIL & _).
  assert (KEEP : forall a,
      (fuzz_alloc_ran_out_c.G_RAN_OUT <= a < fuzz_alloc_ran_out_c.G_RAN_OUT + 1 \/
       GL_OWN_RAN_OUT <= a < GL_OWN_RAN_OUT + 1) -> mbyte segs mem a = mbyte segs mem0 a).
  { intros a Ha. pose proof Ha as Ha2. apply rtt_flag_img in Ha2. destruct Ha2 as (Hi & Hn & Hs).
    apply (IMc a Hi Hn).
    - unfold rwin. pose proof (HIL a Hi) as Hlo. intros [Hr|Hr]; [lia|].
      rewrite ERRB in Hr. unfold strtod_c.STRTOD_ERRNO, fuzz_alloc_ran_out_c.G_RAN_OUT, GL_RAN_OUT, GL_OWN_RAN_OUT in *.
      lia.
    - unfold rtt_writes. intros [[H _]|H]; [apply H; reflexivity | exact (Hs H)]. }
  split; [exact R1|]. split; [exact R2|]. split.
  - apply (ia_bytes mem0); [exact B1|]. intros i Hi. rewrite Mem.length_le1 in Hi. apply KEEP. lia.
  - apply (ia_bytes mem0); [exact B2|]. intros i Hi. rewrite Mem.length_le1 in Hi. apply KEEP. lia.
Qed.

(* ---- the stages of the walk, last first; each ends in rtt_post ---- *)

(* 0x15488: same(doc, &back) returned nonzero; the copy branch (memcpy to copy, or pj_free of back), a0 := 0 *)
Definition stg_end_st : Prop :=
  forall L0 A0 regs0 mem0 md0 Lam0 peak0 cnt0 b0 doc pretty copy t D ro oo
    fx' L A regs mem md Lam peak Db s2v s3v s4v s5v,
  let p := negb (pretty =? 0) in
  rtt_ent L0 A0 regs0 mem0 md0 Lam0 peak0 cnt0 b0 doc pretty copy t D ->
  rtt_fl mem0 ro oo -> ro = 0 -> oo = 0 ->
  rtt_inv L0 A0 regs0 mem0 md0 Lam0 peak0 doc copy t D fx' L A mem md Db Lam peak
    (cnt0 + wcalls t p + Z.of_nat (PjRoundTrip.tcalls t)) (rtt_bf F b0 cnt0 t p) ->
  rtt_regs regs0 regs copy s2v s3v s4v s5v ->
  pj_node segs mem (lin Lam) (spZ regs0 - 112) t Db -> new_blks L0 A0 Db -> (forall bk, In bk Db -> In bk Lam) ->
  Permutation (map snd Db) (map Z.of_nat (lsz (PjRoundTrip.ttrace t))) ->
  Z.of_nat (length Db) = nlive (PjRoundTrip.ttrace t) ->
  SR segs (mkCfg (@mkst fx' regs (Z_to_bv 64 0x15488) mem (seg_rom segs)) md)
    (rtt_post L0 A0 regs0 mem0 md0 Lam0 peak0 cnt0 b0 doc pretty copy t D ro oo).

(* 0x15460: free (want) and fuzz_free (text) returned; the two flag tests (both 0), rc = 0, same(doc, &back) *)
Definition stg_same_st : Prop :=
  forall L0 A0 regs0 mem0 md0 Lam0 peak0 cnt0 b0 doc pretty copy t D ro oo
    fx' L A regs mem md Lam peak Db s2v s3v,
  let p := negb (pretty =? 0) in
  rtt_ent L0 A0 regs0 mem0 md0 Lam0 peak0 cnt0 b0 doc pretty copy t D ->
  rtt_fl mem0 ro oo -> ro = 0 -> oo = 0 ->
  rtt_inv L0 A0 regs0 mem0 md0 Lam0 peak0 doc copy t D fx' L A mem md Db Lam peak
    (cnt0 + wcalls t p + Z.of_nat (PjRoundTrip.tcalls t)) (rtt_bf F b0 cnt0 t p) ->
  rtt_regs regs0 regs copy s2v s3v (Z_to_bv 64 0) (Z_to_bv 64 0x353d0) ->
  pj_node segs mem (lin Lam) (spZ regs0 - 112) t Db -> new_blks L0 A0 Db -> (forall bk, In bk Db -> In bk Lam) ->
  Permutation (map snd Db) (map Z.of_nat (lsz (PjRoundTrip.ttrace t))) ->
  Z.of_nat (length Db) = nlive (PjRoundTrip.ttrace t) ->
  SR segs (mkCfg (@mkst fx' regs (Z_to_bv 64 0x15460) mem (seg_rom segs)) md)
    (rtt_post L0 A0 regs0 mem0 md0 Lam0 peak0 cnt0 b0 doc pretty copy t D ro oo).

(* 0x1544c: parse_noting returned rc = 0 (back read to t); s4 := rc, free (want), fuzz_free (text) *)
Definition stg_ff_st : Prop :=
  forall L0 A0 regs0 mem0 md0 Lam0 peak0 cnt0 b0 doc pretty copy t D ro oo
    fx' L A regs mem md Lam peak Db q want len cap,
  let p := negb (pretty =? 0) in
  rtt_ent L0 A0 regs0 mem0 md0 Lam0 peak0 cnt0 b0 doc pretty copy t D ->
  rtt_fl mem0 ro oo -> ro = 0 -> oo = 0 ->
  rtt_inv L0 A0 regs0 mem0 md0 Lam0 peak0 doc copy t D fx' L A mem md (Db ++ [(q, wcap t p)]) Lam peak
    (cnt0 + wcalls t p + Z.of_nat (PjRoundTrip.tcalls t)) (rtt_bp F b0 cnt0 t p) ->
  rtt_regs regs0 regs copy (Z_to_bv 64 q) (Z_to_bv 64 want) (getr regs0 20) (Z_to_bv 64 0x353d0) ->
  getr regs 10 = Z_to_bv 64 0 ->
  rt_text L0 A0 mem Lam t p q ->
  0 <= want < 2 ^ 64 -> 0 < cap -> In (want, cap) (blocks L A) -> len < cap ->
  cap = tx_capf 0 0 (rtt_ns t p) ->
  (forall i, 0 <= i < cap -> ~ in_img B (want + i)) ->
  (forall a k, In (a, k) (blocks L0 A0) -> 0 < k -> a <> want) ->
  (forall a n, In (a, n) Lam -> a - 16 <> want) ->
  pj_node segs mem (lin Lam) (spZ regs0 - 112) t Db -> new_blks L0 A0 Db -> (forall bk, In bk Db -> In bk Lam) ->
  Permutation (map snd Db) (map Z.of_nat (lsz (PjRoundTrip.ttrace t))) ->
  Z.of_nat (length Db) = nlive (PjRoundTrip.ttrace t) ->
  SR segs (mkCfg (@mkst fx' regs (Z_to_bv 64 0x1544c) mem (seg_rom segs)) md)
    (rtt_post L0 A0 regs0 mem0 md0 Lam0 peak0 cnt0 b0 doc pretty copy t D ro oo).

(* 0x153e4: the ran-out arm (a flag byte is nonzero): free (want), fuzz_free (text), a0 := 1 *)
Definition stg_oom_st : Prop :=
  forall L0 A0 regs0 mem0 md0 Lam0 peak0 cnt0 b0 doc pretty copy t D ro oo
    fx' L A regs mem md Lam peak q want len cap s4v s5v,
  let p := negb (pretty =? 0) in
  rtt_ent L0 A0 regs0 mem0 md0 Lam0 peak0 cnt0 b0 doc pretty copy t D ->
  rtt_fl mem0 ro oo -> (ro <> 0 \/ oo <> 0) ->
  rtt_inv L0 A0 regs0 mem0 md0 Lam0 peak0 doc copy t D fx' L A mem md [(q, wcap t p)] Lam peak
    (cnt0 + wcalls t p) (rtt_bt F b0 cnt0 t p) ->
  rtt_regs regs0 regs copy (Z_to_bv 64 q) (Z_to_bv 64 want) s4v s5v ->
  rt_text L0 A0 mem Lam t p q ->
  0 <= want < 2 ^ 64 -> 0 < cap -> In (want, cap) (blocks L A) -> len < cap ->
  cap = tx_capf 0 0 (rtt_ns t p) ->
  (forall i, 0 <= i < cap -> ~ in_img B (want + i)) ->
  (forall a k, In (a, k) (blocks L0 A0) -> 0 < k -> a <> want) ->
  (forall a n, In (a, n) Lam -> a - 16 <> want) ->
  SR segs (mkCfg (@mkst fx' regs (Z_to_bv 64 0x153e4) mem (seg_rom segs)) md)
    (rtt_post L0 A0 regs0 mem0 md0 Lam0 peak0 cnt0 b0 doc pretty copy t D ro oo).

(* 0x153b8: rendered() done; lw failed (0), ld want, the flag tests (ran out: stg_oom), strcmp, strlen, parse_noting *)
Definition stg_cmp_st : Prop :=
  forall L0 A0 regs0 mem0 md0 Lam0 peak0 cnt0 b0 doc pretty copy t D ro oo
    fx' L A regs mem md Lam peak q want cap s3v,
  let p := negb (pretty =? 0) in
  rtt_ent L0 A0 regs0 mem0 md0 Lam0 peak0 cnt0 b0 doc pretty copy t D ->
  rtt_fl mem0 ro oo ->
  rtt_inv L0 A0 regs0 mem0 md0 Lam0 peak0 doc copy t D fx' L A mem md [(q, wcap t p)] Lam peak
    (cnt0 + wcalls t p) (rtt_bt F b0 cnt0 t p) ->
  rtt_regs regs0 regs copy (Z_to_bv 64 q) s3v (getr regs0 20) (getr regs0 21) ->
  rt_text L0 A0 mem Lam t p q ->
  rt_harn L0 A0 L A mem Lam (spZ regs0 - 112) want (wlen t p) cap (map (Z_to_bv 8) (wdoc t p)) ->
  cap = tx_capf 0 0 (rtt_ns t p) ->
  SR segs (mkCfg (@mkst fx' regs (Z_to_bv 64 0x153b8) mem (seg_rom segs)) md)
    (rtt_post L0 A0 regs0 mem0 md0 Lam0 peak0 cnt0 b0 doc pretty copy t D ro oo).

(* 0x153a0: tx_value returned; tx_put "\n" when pretty *)
Definition stg_nl_st : Prop :=
  forall L0 A0 regs0 mem0 md0 Lam0 peak0 cnt0 b0 doc pretty copy t D ro oo
    fx' L A regs mem md Lam peak q want cap,
  let p := negb (pretty =? 0) in
  rtt_ent L0 A0 regs0 mem0 md0 Lam0 peak0 cnt0 b0 doc pretty copy t D ->
  rtt_fl mem0 ro oo ->
  rtt_inv L0 A0 regs0 mem0 md0 Lam0 peak0 doc copy t D fx' L A mem md [(q, wcap t p)] Lam peak
    (cnt0 + wcalls t p) (tx_fold F (rtt_bw F b0 cnt0 t p) 0 0 ([0] ++ tv_calls t p 0)) ->
  rtt_regs regs0 regs copy (Z_to_bv 64 q) (Z_to_bv 64 pretty) (getr regs0 20) (getr regs0 21) ->
  rt_text L0 A0 mem Lam t p q ->
  rt_harn L0 A0 L A mem Lam (spZ regs0 - 112) want (Z.of_nat (length (concat (wvpieces t p 0)))) cap
    (map (Z_to_bv 8) (concat (wvpieces t p 0))) ->
  cap = tx_capf 0 0 ([0] ++ tv_calls t p 0) ->
  SR segs (mkCfg (@mkst fx' regs (Z_to_bv 64 0x153a0) mem (seg_rom segs)) md)
    (rtt_post L0 A0 regs0 mem0 md0 Lam0 peak0 cnt0 b0 doc pretty copy t D ro oo).

(* 0x1538c: tx_put "" returned; tx_value(&t, doc, pretty, 0) *)
Definition stg_txv_st : Prop :=
  forall L0 A0 regs0 mem0 md0 Lam0 peak0 cnt0 b0 doc pretty copy t D ro oo
    fx' L A regs mem md Lam peak q want,
  let p := negb (pretty =? 0) in
  rtt_ent L0 A0 regs0 mem0 md0 Lam0 peak0 cnt0 b0 doc pretty copy t D ->
  rtt_fl mem0 ro oo ->
  rtt_inv L0 A0 regs0 mem0 md0 Lam0 peak0 doc copy t D fx' L A mem md [(q, wcap t p)] Lam peak
    (cnt0 + wcalls t p) (tx_fold F (rtt_bw F b0 cnt0 t p) 0 0 [0]) ->
  rtt_regs regs0 regs copy (Z_to_bv 64 q) (Z_to_bv 64 pretty) (getr regs0 20) (getr regs0 21) ->
  rt_text L0 A0 mem Lam t p q ->
  rt_harn L0 A0 L A mem Lam (spZ regs0 - 112) want 0 2 [] ->
  SR segs (mkCfg (@mkst fx' regs (Z_to_bv 64 0x1538c) mem (seg_rom segs)) md)
    (rtt_post L0 A0 regs0 mem0 md0 Lam0 peak0 cnt0 b0 doc pretty copy t D ro oo).

(* 0x15364: pj_write returned the text q in a0; s2 := q, the 32-byte record zeroed, tx_put(&t, "", 0) *)
Definition stg_tx1_st : Prop :=
  forall L0 A0 regs0 mem0 md0 Lam0 peak0 cnt0 b0 doc pretty copy t D ro oo
    fx' L A regs mem md Lam peak q,
  let p := negb (pretty =? 0) in
  rtt_ent L0 A0 regs0 mem0 md0 Lam0 peak0 cnt0 b0 doc pretty copy t D ->
  rtt_fl mem0 ro oo ->
  rtt_inv L0 A0 regs0 mem0 md0 Lam0 peak0 doc copy t D fx' L A mem md [(q, wcap t p)] Lam peak
    (cnt0 + wcalls t p) (rtt_bw F b0 cnt0 t p) ->
  rtt_regs regs0 regs copy (getr regs0 18) (Z_to_bv 64 pretty) (getr regs0 20) (getr regs0 21) ->
  getr regs 10 = Z_to_bv 64 q ->
  rt_text L0 A0 mem Lam t p q ->
  SR segs (mkCfg (@mkst fx' regs (Z_to_bv 64 0x15364) mem (seg_rom segs)) md)
    (rtt_post L0 A0 regs0 mem0 md0 Lam0 peak0 cnt0 b0 doc pretty copy t D ro oo).

End P.
