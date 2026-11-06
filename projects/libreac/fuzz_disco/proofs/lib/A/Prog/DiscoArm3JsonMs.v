From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP09 YI04 YI09 YI08 YI00 YN3v YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YE00 YE01 YO09.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal DiscoSyms DiscoList DiscoAddr DiscoPa DiscoPaLib DiscoBase DiscoFrame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
DiscoEntryInv DiscoArm3 DiscoArm3JsonModel DiscoArm3JsonCut DiscoEntBodyStmt.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ disco_listing PI).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).
Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.

Definition ms_in (cx : dcx) (h i n now op : Z) (W0 : world SEGS) (c0 : config) (T0 T1 : list byte) (buf : Z)
  (ret c : Z) (R : bvmap 5 word -> Prop) (X : world SEGS -> (word -> option byte) -> Prop)
  : world SEGS -> config -> Prop :=
  jcut B MT XM_LIB RLO RHI tfib_K cx h i n now op W0 c0 T0 T1 buf (SIGMA DS___asan_memset - BASE) dsh_scr
    (fun regs => getr regs 1 = w64 (BASE + ret) /\ getr regs 10 = w64 (jcur cx c) /\ getr regs 11 = w64 0 /\
       getr regs 12 = w64 144 /\ R regs) X.

Definition ms_out (cx : dcx) (h i n now op : Z) (W0 : world SEGS) (c0 : config) (T0 T1 : list byte) (buf : Z)
  (ret c : Z) (R : bvmap 5 word -> Prop) (X : world SEGS -> (word -> option byte) -> Prop)
  : world SEGS -> config -> Prop :=
  jcut B MT XM_LIB RLO RHI tfib_K cx h i n now op W0 c0 T0 T1 buf ret dsh_scr
    (fun regs => getr regs 10 = w64 (jcur cx c) /\ R regs)
    (fun W m => X W m /\ garr8 SEGS (rd W m) (jcur cx c) (repeat 0 144)).

Definition ms_kept (cx : dcx) (c : Z) (W : world SEGS) (m : word -> option byte) (W' : world SEGS)
  (m' : word -> option byte) : Prop :=
  W' = W /\ d_kept (fun a => d_A cx - ESTACK <= a < d_A cx \/ jcur cx c <= a < jcur cx c + 144) W m W' m'.

Definition ms_step_stmt : Prop :=
  forall (cx : dcx) (h i n now op : Z) (W0 : world SEGS) (c0 : config) (T0 T1 : list byte) (buf : Z)
    (ret c : Z) (R : bvmap 5 word -> Prop) (X : world SEGS -> (word -> option byte) -> Prop)
    (W : world SEGS) (cf : config),
  0 <= ret < 2 ^ 40 -> ret mod 2 = 0 -> 0 <= c <= 8 ->
  (forall rg rg', aregs_preserved rg rg' -> R rg -> R rg') ->
  (forall W1 m1 W2 m2, X W1 m1 -> ms_kept cx c W1 m1 W2 m2 -> X W2 m2) ->
  ms_in cx h i n now op W0 c0 T0 T1 buf ret c R X W cf ->
  SRr SEGS W cf (ms_out cx h i n now op W0 c0 T0 T1 buf ret c R X).

End h.
End f.
End d.

From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP0m YP03.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import DiscoEntSeatStmt DiscoEntSeat DiscoACjr DiscoEntBody.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import slot_inv.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Section d2. Context {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Section f2.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ disco_listing PI).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).

Lemma ms_rok : forall (E : env) (H : word -> bool) (m m' : word -> option byte) (r : YP09.region) (P : Z -> Prop),
  region_ok SEGS E (mrestrict H m) r -> forallb (chunk_inside r) (YP09.r_chunks r) = true ->
  (forall a, apresent H m a -> apresent H m' a) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ P a -> aview SEGS H m' a = aview SEGS H m a) ->
  (forall c, In c (YP09.r_chunks r) -> forall i, 0 <= i < YP09.c_len c ->
     ~ P (base_val E (YP09.r_base r) + YP09.c_off c + i)) ->
  region_ok SEGS E (mrestrict H m') r.
Proof.
intros E H m m' r P HR Hci Hp Hk Hc.
unfold region_ok in HR |- *. cbv zeta in HR |- *.
destruct HR as (Hlo & Hhi & Hw & Hcs).
split; [exact Hlo|]. split; [exact Hhi|]. split.
- intros o Ho. apply (writable_kept H m m' _ (Hp _)). apply Hw. exact Ho.
- apply Forall_forall. intros c Hcin.
  pose proof (proj1 (Forall_forall _ _) Hcs c Hcin) as Hck.
  pose proof (proj1 (forallb_forall _ _) Hci c Hcin) as Hin. unfold chunk_inside in Hin.
  apply andb_prop in Hin as [Hin Hc3]. apply andb_prop in Hin as [Hc1 Hc2].
  apply Z.leb_le in Hc1. apply Z.leb_le in Hc2. apply Z.leb_le in Hc3.
  intros i Hi. destruct (Hck i Hi) as (b & Hb1 & Hb2). exists b. split; [exact Hb1|].
  rewrite (mbyte_of_aview SEGS H H m m'); [exact Hb2|].
  apply Hk; [|exact (Hc c Hcin i Hi)]. unfold YP09.c_len in *. lia.
Qed.

Lemma ms_chunks_ext : forall (r : YP09.region) (b : Z) (P : Z -> Prop),
  forallb (chunk_inside r) (YP09.r_chunks r) = true ->
  (forall a, b + YP09.r_lo r <= a < b + YP09.r_hi r -> ~ P a) ->
  forall c, In c (YP09.r_chunks r) -> forall i, 0 <= i < YP09.c_len c -> ~ P (b + YP09.c_off c + i).
Proof.
intros r b P Hci HP c Hcin i Hi.
pose proof (proj1 (forallb_forall _ _) Hci c Hcin) as Hin. unfold chunk_inside in Hin.
apply andb_prop in Hin as [Hin Hc3]. apply andb_prop in Hin as [Hc1 Hc2].
apply Z.leb_le in Hc1. apply Z.leb_le in Hc2. apply Z.leb_le in Hc3.
apply HP. unfold YP09.c_len in *. lia.
Qed.

Lemma ms_rdword : forall (r r' : Z -> option Z) a,
  (forall j, 0 <= j < 8 -> r' (a + j) = r (a + j)) -> rdword r' a = rdword r a.
Proof.
intros r r' a H. unfold rdword.
assert (H0 : r' a = r a) by (rewrite <- (Z.add_0_r a); apply H; lia).
rewrite H0, (H 1), (H 2), (H 3), (H 4), (H 5), (H 6), (H 7) by lia. reflexivity.
Qed.

Lemma ms_garr8_zero : forall (H : word -> bool) (m : word -> option byte) d (n : nat),
  (forall i, 0 <= i < Z.of_nat n -> aview SEGS H m (d + i) = Some 0) ->
  garr8 SEGS (mrestrict H m) d (repeat 0 n).
Proof.
intros H m d n Hz j Hj. rewrite repeat_length in Hj. rewrite nth_repeat. split; [|lia].
intros kk Hkk. assert (kk = 0%nat) by lia. subst kk.
specialize (Hz (Z.of_nat j) ltac:(lia)). unfold aview in Hz.
cbn [Z.of_nat]. rewrite Z.add_0_r.
destruct (mbyte SEGS (mrestrict H m) (d + Z.of_nat j)) as [b|] eqn:Eb; [|discriminate Hz].
cbn [option_map] in Hz. injection Hz as Hb. f_equal. apply bv_eq. rewrite Hb. vm_compute. reflexivity.
Qed.

Section h2.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis AMEMSET : forall fq : YK11.FPState, aintrin_realizes (fx := fq) SEGS B OSet (SIGMA DS___asan_memset).

Theorem ms_step : ms_step_stmt B MT XM_LIB RLO RHI tfib_K.
Proof.
intros cx h i n now op W0 c0 T0 T1 buf ret c R X W cf Hret Hret2 Hc HRp HXk Hin.
unfold ms_in, jcut in Hin.
destruct Hin as (HFROM & Hat).
unfold d_arm_at_pf, d_at in Hat.
destruct Hat as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & -> & HCSR & HBASE & HJ & HFR & Hk & Hnev & HMO & Hacc &
  Hi & Hn & Hnow & HRL & (R22 & R26 & R1 & R10 & R11 & R12 & HR) & (HSP1 & HTAB & HBUF & HX) & HSP0 & HBODY).
assert (HCTX : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k) by exact (conj HBASE (conj HJ HFR)).
pose proof (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k HCTX)
  as (GS16 & GSlo & GShi & GF4096 & GFceil & GFapp & GFoff & GF32 & GFpres & GFshp & GSTK & HAR3 & HFin3 & EFA3 & EFL3).
pose proof alloc_ceiling_value as Hceil0.
pose proof (d_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (GA1 & GA32).
unfold MFRAME in GA1. unfold LLVMF_STK in GSlo.
pose proof HBODY as (T & G & Lk & HH & HFRM & HSHD & HOBJ & HBLK & HINP & HIMG & HOFFF & HGEO & HDCAN & HSTKF & HAWRF).
pose proof HFRM as (E & HE & HREG & HFLAG & H216 & H152).
pose proof HBLK as (HPerm0 & _ & _ & _).
pose proof HRL as (L2 & L3 & L4 & L8 & L9 & L18 & L20 & L25).
assert (HJC : jcur cx c = d_FB cx + 240 + 144 * c) by (unfold jcur, d_obj, dobj_off; lia).
assert (HZ : forall kk, 30 <= kk < 192 -> dsh_scr kk = 0).
{ intros kk Hkk.
  assert (Hb : forallb (fun k => Z.eqb (dsh_scr (Z.of_nat k)) 0) (seq 30 162) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in Hb. specialize (Hb (Z.to_nat kk)). rewrite Z2Nat.id in Hb by lia.
  apply Z.eqb_eq. apply Hb. apply in_seq. lia. }
assert (Epc : BASE + (SIGMA DS___asan_memset - BASE) = SIGMA DS___asan_memset) by lia.
unfold cfg_at. rewrite Epc.
eapply SRr_mono.
{ apply (aj_intrin_at SEGS B LAWS pa_segs_low OSet (SIGMA DS___asan_memset) (AMEMSET fq) W regs mem3
    LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(DFRAME_CLASS, c_fpos cx)] ly3 S3 md3 k
    (jcur cx c) 0 144 (d_A cx - d_S cx) (w64 (BASE + ret)) HJ R10 R11 R12).
  - lia.
  - lia.
  - lia.
  - rewrite L2. lia.
  - pose proof (Z.div_mod (d_A cx) 32 ltac:(lia)) as DA. pose proof (Z.div_mod (d_S cx) 16 ltac:(lia)) as DS.
    rewrite GA32 in DA. rewrite GS16 in DS.
    replace (d_A cx - d_S cx) with ((2 * (d_A cx / 32) - d_S cx / 16) * 16) by lia. apply Z_mod_mult.
  - lia.
  - unfold ESTACK, LLVMF_STK. lia.
  - exact L3.
  - exact L4.
  - exact R1.
  - exact (ret_ok_codeptr_v ret Hret Hret2).
  - intros a Ha. split.
    + apply (proj1 (HAWRF a ltac:(unfold DFRAME_SIZE; lia))).
    + unfold ESTACK. lia.
  - unfold amem_range. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in GFapp.
    unfold kLowMemEnd, kHighMemBeg, kHighMemEnd. lia.
  - intros x Hx. exists 0. split; [|left; reflexivity]. unfold shadow_of_addr.
    replace (SHADOW_OFF + x / 8) with (shadow_addr (d_FB cx) + (x / 8 - d_FB cx / 8)) by (unfold shadow_addr; lia).
    rewrite HSHD by (unfold DFRAME_SH; lia). rewrite HZ by lia. reflexivity.
  - intros _ s Hs. replace s with (shadow_addr (d_FB cx) + (s - shadow_addr (d_FB cx))) by lia.
    rewrite HSHD by (unfold DFRAME_SH; unfold shadow_addr in *; lia). discriminate.
  - exact I. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & H10' & HSET & HKEEP & HPRES).
assert (HKD : forall a, 0 <= a < 2 ^ 64 -> ~ (d_A cx - ESTACK <= a < d_A cx \/ jcur cx c <= a < jcur cx c + 144) ->
  aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) mem3 a).
{ intros a Ha Hna. apply HKEEP; [exact Ha | intros H'; apply Hna; right; exact H' | intros H'; apply Hna; left; lia]. }
assert (HSA : 0 <= shadow_addr (d_FB cx) /\ shadow_addr (d_FB cx) + 512 <= alloc_ceiling /\
  (shadow_addr (d_FB cx) + 512 <= d_FB cx \/ d_FB cx + 4096 <= shadow_addr (d_FB cx))).
{ unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in GFapp. unfold shadow_addr, SHADOW_OFF. lia. }
assert (KV : forall off v, 0 <= off -> off + 8 <= 472 ->
  val_mem SEGS (rd W mem3) (d_A cx + off) 8 v -> val_mem SEGS (rd W mem2) (d_A cx + off) 8 v).
{ intros off v Ho1 Ho2 Hv. apply (val_mem_kept SEGS (w_H W) (w_H W) mem3 mem2); [|exact Hv].
  intros kk Hkk. change (Z.of_nat 8) with 8 in Hkk. apply HKD; [lia|]. unfold ESTACK. lia. }
assert (UA : bv_unsigned (ew E AT_A) = d_A cx).
{ rewrite (proj1 (proj2 (proj2 (proj2 HE)))). apply unsigned_lit_small. lia. }
assert (UF : bv_unsigned (ew E AT_F) = d_FB cx).
{ rewrite (proj1 (proj2 (proj2 (proj2 (proj2 HE))))). apply unsigned_lit_small. lia. }
assert (USH : bv_unsigned (ew E AT_SH) = shadow_addr (d_FB cx)).
{ rewrite (proj2 (proj2 (proj2 (proj2 (proj2 HE))))). apply unsigned_lit_small. lia. }
assert (US : bv_unsigned (ew E AT_STK) = d_S cx).
{ rewrite (proj1 HE AT_STK 2%bv eq_refl). reflexivity. }
pose (PK := fun a : Z => d_A cx - ESTACK <= a < d_A cx \/ jcur cx c <= a < jcur cx c + 144).
assert (HFRM2 : d_frame cx h dsh_scr W mem2).
{ exists E. split; [exact HE|]. split.
  - apply Forall_forall. intros r Hr. pose proof (proj1 (Forall_forall _ _) HREG r Hr) as HRr.
    unfold d_regions in Hr. destruct Hr as [<- | [<- | [<- | [<- | []]]]].
    + apply (ms_rok E (w_H W) mem3 mem2 _ PK HRr ltac:(vm_compute; reflexivity) HPRES HKD).
      apply (ms_chunks_ext _ _ PK); [vm_compute; reflexivity|].
      cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite US. intros a Ha. unfold PK, ESTACK. lia.
    + apply (ms_rok E (w_H W) mem3 mem2 _ PK HRr ltac:(vm_compute; reflexivity) HPRES HKD).
      apply (ms_chunks_ext _ _ PK); [vm_compute; reflexivity|].
      cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite UA. intros a Ha. unfold PK, ESTACK. lia.
    + apply (ms_rok E (w_H W) mem3 mem2 _ PK HRr ltac:(vm_compute; reflexivity) HPRES HKD).
      intros cc Hcc ii Hii. cbn [YP09.r_chunks YP09.r_base base_val] in Hcc |- *. rewrite UF.
      destruct Hcc as [<- | [<- | [<- | []]]]; cbn [YP09.c_off YP09.c_len YP09.c_val cv_len] in Hii |- *;
        try change (Z.of_N 8) with 8 in Hii; unfold PK, ESTACK; lia.
    + apply (ms_rok E (w_H W) mem3 mem2 _ PK HRr ltac:(vm_compute; reflexivity) HPRES HKD).
      apply (ms_chunks_ext _ _ PK); [vm_compute; reflexivity|].
      unfold fshadow_region. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite USH.
      change (fs_frame_bytes DFRAME_CLASS / 8) with 512. intros a Ha. unfold PK, ESTACK. lia.
  - split.
    + rewrite (ms_rdword (aview SEGS (w_H W) mem3) (aview SEGS (w_H W) mem2)); [exact HFLAG|].
      intros j Hj. change (fs_frame_bytes DFRAME_CLASS) with 4096. apply HKD; [lia|]. unfold ESTACK. lia.
    + split; [apply KV; [lia | lia | exact H216] | apply KV; [lia | lia | exact H152]]. }
assert (HSHD2 : d_shadow cx dsh_scr W mem2).
{ intros kk Hkk. unfold DFRAME_SH in Hkk.
  rewrite HKD; [exact (HSHD kk ltac:(unfold DFRAME_SH; lia)) | lia |]. unfold ESTACK. lia. }
assert (Hinb : In (buf, Z.max (slot_ser_defs.ser_cap op) 1) (ablocks B ly3 S3)).
{ apply (Permutation_in _ (Permutation_sym HPerm0)). unfold a3_xb. cbn [app]. left. reflexivity. }
assert (Hinh : In (h, HUNT_SIZE) (ablocks B ly3 S3)).
{ apply (Permutation_in _ (Permutation_sym HPerm0)). unfold a3_xb. cbn [app]. right. left. reflexivity. }
pose proof (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hinb) as (_ & Hb4096 & Hbceil & _ & _ & _ & _).
pose proof (sep_block_frame SEGS B LAWS ly3 S3 W mem3 md3 _ _ _ _ HAR3 Hinb HFin3) as Hbsep.
rewrite EFA3 in Hbsep. unfold zdisjoint in Hbsep. cbn [fst snd] in Hbsep.
change (fs_frame_bytes DFRAME_CLASS) with 4096 in Hbsep.
assert (Hrq : req_size (Z.max (slot_ser_defs.ser_cap op) 1) = Z.max (slot_ser_defs.ser_cap op) 1).
{ unfold req_size. destruct (Z.eqb_spec (Z.max (slot_ser_defs.ser_cap op) 1) 0); lia. }
rewrite Hrq in Hbsep, Hbceil.
assert (P2 : getr regs2 2 = getr regs 2) by exact (HP2 2 ltac:(unfold acallee_saved; lia)).
assert (P3 : getr regs2 3 = getr regs 3) by exact (HP2 3 ltac:(unfold acallee_saved; lia)).
assert (P4 : getr regs2 4 = getr regs 4) by exact (HP2 4 ltac:(unfold acallee_saved; lia)).
assert (P8 : getr regs2 8 = getr regs 8) by exact (HP2 8 ltac:(unfold acallee_saved; lia)).
assert (P9 : getr regs2 9 = getr regs 9) by exact (HP2 9 ltac:(unfold acallee_saved; lia)).
assert (P18 : getr regs2 18 = getr regs 18) by exact (HP2 18 ltac:(unfold acallee_saved; lia)).
assert (P20 : getr regs2 20 = getr regs 20) by exact (HP2 20 ltac:(unfold acallee_saved; lia)).
assert (P22 : getr regs2 22 = getr regs 22) by exact (HP2 22 ltac:(unfold acallee_saved; lia)).
assert (P25 : getr regs2 25 = getr regs 25) by exact (HP2 25 ltac:(unfold acallee_saved; lia)).
assert (P26 : getr regs2 26 = getr regs 26) by exact (HP2 26 ltac:(unfold acallee_saved; lia)).
pose proof HSP1 as ((H232 & H344) & H224 & H248).
assert (HSP0' : d_sp0 cx i now W mem2) by (split; apply KV; first [lia | assumption]).
unfold ms_out, jcut. split; [exact HFROM|].
unfold d_arm_at_pf, d_at.
exists fq, ly3, S3, regs2, mem2, md2, k, acc.
split; [unfold cfg_at; reflexivity|].
split; [exact HCSR|]. split; [exact HBASE|]. split; [exact HJ2|]. split; [exact HFR|]. split; [exact Hk|]. split; [exact Hnev|].
split; [exact HMO|]. split; [exact Hacc|]. split; [exact Hi|]. split; [exact Hn|]. split; [exact Hnow|].
split.
{ split; [unfold spZ in *; rewrite P2; exact L2|].
  split; [rewrite P3; exact L3|]. split; [rewrite P4; exact L4|]. split; [rewrite P8; exact L8|].
  split; [rewrite P9; exact L9|]. split; [rewrite P18; exact L18|]. split; [rewrite P20; exact L20|].
  rewrite P25; exact L25. }
split.
{ split; [rewrite P22; exact R22|]. split; [rewrite P26; exact R26|]. split; [exact H10'|].
  exact (HRp regs regs2 HP2 HR). }
split.
{ split.
  { split; [exact HSP0'|]. split; apply KV; first [lia | assumption]. }
  split.
  { destruct HTAB as (Hage & HT1). split; [exact Hage|].
    destruct Hage as (removed & Hm & Hpost). pose proof (proj1 Hpost) as HL1.
    apply (garr8_frame SEGS (rd W mem3) (rd W mem2) (d_obj cx OT) _ HT1).
    intros a Ha. rewrite length_map, HL1 in Ha. unfold d_obj, dobj_off in Ha.
    apply (mbyte_of_aview SEGS). apply HKD; [lia|]. unfold ESTACK. lia. }
  split.
  { destruct HBUF as (Hr & HB). split; [exact Hr|].
    apply (garr8_frame SEGS (rd W mem3) (rd W mem2) buf _ HB).
    intros a Ha. rewrite length_app, Nat2Z.inj_add in Ha. cbn [length Z.of_nat] in Ha. unfold a3_r in Hr.
    apply (mbyte_of_aview SEGS). apply HKD; [lia|]. unfold ESTACK. lia. }
  split.
  { apply (HXk W mem3 W mem2 HX). split; [reflexivity|]. exact HKD. }
  apply ms_garr8_zero. intros ii Hii. change (Z.of_nat 144) with 144 in Hii.
  rewrite (HSET ii Hii). reflexivity. }
split; [exact HSP0'|].
apply (d_body_rt B cx h n n (a3_xb buf op) dsh_scr dsh_scr ly3 S3 W mem3 mem2 (d_A cx - ESTACK) (d_A cx)
  (fun a => d_A cx - ESTACK <= a < d_A cx \/ jcur cx c <= a < jcur cx c + 144) HBODY).
- unfold ESTACK, LLVMF_STK. lia.
- lia.
- intros a [Ha | Ha]; [left; exact Ha | right]. intros Hrd.
  unfold d_rdset, d_objr, d_obj, dobj_off, dobj_size in Hrd.
  destruct Hrd as [Hrd | [Hrd | [Hrd | [Hrd | [Hrd | [(Hcn & Hrd) | [Hrd | Hrd]]]]]]].
  + lia.
  + lia.
  + lia.
  + lia.
  + pose proof (sep_block_frame SEGS B LAWS ly3 S3 W mem3 md3 _ _ _ _ HAR3 Hinh HFin3) as Hs.
    rewrite EFA3 in Hs. unfold zdisjoint in Hs. cbn [fst snd] in Hs.
    change (fs_frame_bytes DFRAME_CLASS) with 4096 in Hs. change (req_size HUNT_SIZE) with 480 in Hs.
    unfold HUNT_SIZE in Hrd. lia.
  + pose proof HBASE as ((_ & _ & _ & _ & Hpn & _) & _).
    destruct Hpn as [(Hn0 & _) | (_ & Hin0)]; [lia|].
    assert (Hinp : In (c_p cx, c_n cx) (ablocks B ly3 S3)).
    { apply (Permutation_in _ (Permutation_sym HPerm0)). unfold a3_xb. cbn [app]. right. right. exact Hin0. }
    pose proof (sep_block_frame SEGS B LAWS ly3 S3 W mem3 md3 _ _ _ _ HAR3 Hinp HFin3) as Hs.
    rewrite EFA3 in Hs. unfold zdisjoint in Hs. cbn [fst snd] in Hs.
    change (fs_frame_bytes DFRAME_CLASS) with 4096 in Hs. revert Hs. unfold req_size.
    destruct (Z.eqb_spec (c_n cx) 0); intros Hs; lia.
  + assert (Himg : in_img SEGS a).
    { destruct Hrd as ([(s & Hs & _ & Hsa) | Hrd] & _ & _); [exists s; split; [exact Hs | exact Hsa] | exact (pa_relro_img a Hrd)]. }
    pose proof (pa_img_range a Himg) as Hra. unfold off_img in GFoff. lia.
  + unfold off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP in GFoff. unfold AE2k.FF_canary in Hrd. lia.
- exact HKD.
- intros a _ Ha. exact (HPRES a Ha).
- exact HFRM2.
- exact HSHD2.
- lia.
Qed.
End h2.
End f2.
End d2.
