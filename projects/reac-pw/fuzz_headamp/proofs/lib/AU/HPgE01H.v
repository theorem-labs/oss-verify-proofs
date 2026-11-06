(* reac-pw/fuzz_headamp image B (fuzz_headamp.asan-ubsan, pinned sha256
   53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94; every address measured on the unstripped twin
   1674e30a0698f381704e66d2398d7906c881f4ba8fc619cb41b89fb97ad112ff, same loaded bytes except .note.gnu.build-id): part 2 of segment E01 of the
   walk of LLVMFuzzerTestOneInput, 0x80cc4 (the return of the class-4 frame call) -> 0x80f10 (the target of the size
   test), lib/AU/HPgE01D.v e01u_hdr_stmt. Proves no function (kind: segment lemma of LLVMFuzzerTestOneInput's walk,
   one of its four parts).

   THE CODE (lib/AU/HPgE01D.v E01U_TBL):
     0x80cc4 .. 0x80cd4  mv s7,a0; j 0x80cd0; mv s5,s7; bnez s7 (taken: F >= 4096, so the real-stack arm
                         0x80cd8 .. 0x80cf0 and its probe loop are in no run)
     0x80cf4             sd s5,0x170(s1): R+0x170 = F
     0x80cf8 .. 0x80d30  F[0] = 0x41b58ab3, F[8] = 0x1b958, F[16] = 0x80c40 (0x80d20 .. 0x80d28);
                         s3 = (F >> 3) + K (0x80d04, 0x80d30); a0 = -8, a1 = -14, a2 = -13, a3 = -15
     0x80d34 .. 0x80f04  the 116 `sb` of the frame's shadow (headamp_B_shA), among them `srli a3,s4,0x1a` 0x80d44
     0x80f08             beqz a3 (taken: n < 2 ^ 26; the `j` 0x80f0c is in no run) to 0x80f10.
   THE RUN: one engine state from 0x80cc4 with three written regions: the real-frame cell [R+0x170, R+0x178) (s1,
   atom 9; the stack window), the frame's header [F, F+24) (a0, atom 10) and its 116 shadow bytes from
   shadow_addr F (the extra atom 32, with the alias the code's `srli s3,s5,3` / `add s3,s3,s11` forms); the facts
   4096 <= F (atom 10) and n < 2 ^ 26 (atom 20). The run stops at the size test's `beqz a3`; its not-taken arm is
   refuted (n >> 26 = 0) and the taken arm runs to 0x80f10. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05 YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YK0o.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import Img0U HPgImgB HPgSegM HPgE01D.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require HPgSteps.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ================================ reading a run's last state ================================ *)
Section rdst. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* the frame's 116 shadow bytes, from the chunks of its region (each store leaves the low byte of a
   sign-extended literal) *)
Definition e01h_cvlit1 (v : cval) : option Z :=
match v with
| CVal w (SLit z) => if N.eqb w 1 then Some z else None
| _ => None
end.
Lemma e01h_cvlit1_ok : forall v z, e01h_cvlit1 v = Some z -> v = CVal 1 (SLit z).
Proof.
intros v z H. unfold e01h_cvlit1 in H.
destruct v as [w e | | |]; try discriminate. destruct e; try discriminate.
lazymatch type of H with (if N.eqb w 1 then Some ?j else None) = Some z =>
  destruct (N.eqb_spec w 1); cbn in H; try discriminate; injection H as <-; subst; reflexivity end.
Qed.
Definition e01h_sh_ok (pat : list Z) (i : nat) (c : YP09.chunk) : bool :=
(YP09.c_off c =? Z.of_nat i) &&
match e01h_cvlit1 (YP09.c_val c) with
| Some z => bv_unsigned (byte_of_word (Z_to_bv 64 z) 0) =? nth i pat 0
| None => false
end.
Lemma e01h_fsh_of_region : forall E H mem (k : nat) F lo hi wlo whi cs pat,
region_ok rsegs E (mrestrict H mem) (YP09.mkRegion (Some k) lo hi wlo whi cs) ->
bv_unsigned (ew E k) = shadow_addr F ->
forallb (fun i => existsb (e01h_sh_ok pat i) cs) (seq 0 (length pat)) = true ->
hd_fsh rsegs H mem F pat.
Proof.
intros E H mem k F lo hi wlo whi cs pat (_ & _ & _ & Hcs) Hb Hck i Hi.
assert (Hin : In (Z.to_nat i) (seq 0 (length pat))) by (apply in_seq; lia).
pose proof (proj1 (forallb_forall _ _) Hck _ Hin) as Hx. apply existsb_exists in Hx as ([off v] & Hc & Hok).
unfold e01h_sh_ok in Hok. cbn [YP09.c_off YP09.c_val] in Hok.
apply andb_prop in Hok as [Hoff Hok]. apply Z.eqb_eq in Hoff. rewrite Z2Nat.id in Hoff by lia. subst off.
destruct (e01h_cvlit1 v) as [z|] eqn:Ev; [|discriminate]. apply e01h_cvlit1_ok in Ev. subst v.
apply Z.eqb_eq in Hok.
pose proof (proj1 (Forall_forall _ _) Hcs _ Hc) as Hck1. cbn [YP09.r_base base_val] in Hck1. rewrite Hb in Hck1.
destruct (Hck1 0 ltac:(cbn; lia)) as (b & Hcb & Hmb). cbn [cbyte YP09.c_off YP09.c_val sv_denot] in Hcb, Hmb.
injection Hcb as <-. rewrite Z.add_0_r in Hmb. unfold aview. rewrite Hmb. cbn [option_map]. rewrite Hok. reflexivity.
Qed.
(* a run keeps every byte outside the write windows of its regions *)
Lemma e01h_keep_frame : forall E rs H (m m' : word -> option byte) (P : Z -> Prop),
frame_of E rs (mrestrict H m) (mrestrict H m') -> (forall a, in_wrange E rs a -> P a) ->
forall a, 0 <= a < 2 ^ 64 -> ~ P a -> aview rsegs H m' a = aview rsegs H m a.
Proof.
intros E rs H m m' P HF HW a Ha Hz. unfold aview, mbyte.
rewrite (HF (Z_to_bv 64 a)); [reflexivity|]. rewrite unsigned_lit_small by exact Ha. intros X. exact (Hz (HW a X)).
Qed.
(* a register the state holds as an entry atom *)
Lemma e01h_reg_atom : forall H regs0 extra ss ms (r : bv 5) n,
st_ok rsegs (Ereg regs0 extra) ss (restrict H ms) -> sr_get (ss_regs ss) r = SOff n 0 -> (n < 32)%nat ->
getr (ms_regs ms) r = getr regs0 (Z_to_bv 5 (Z.of_nat n)).
Proof.
intros H regs0 extra ss ms r n HS Hsr Hn.
rewrite (st_ok_restrict_reg rsegs H _ ss ms r HS), Hsr. apply bv_eq. rewrite denot_SOff, Z.add_0_r.
rewrite (ew_Ereg_nat regs0 extra n (Z_to_bv 5 (Z.of_nat n))).
- apply zcanon_id. pose proof (bv_unsigned_in_range _ (getr regs0 (Z_to_bv 5 (Z.of_nat n)))) as Hb.
  change (bv_modulus 64) with (2 ^ 64) in Hb. unfold M64. lia.
- rewrite Z_to_bv_unsigned. symmetry. apply bv_wrap_small. change (bv_modulus 5) with 32. lia.
Qed.
(* the index of the region whose base is atom k *)
Fixpoint e01h_find_base (rs : smem) (k : nat) : nat :=
match rs with
| [] => O
| r :: rs' => match YP09.r_base r with Some k' => if Nat.eqb k k' then O else S (e01h_find_base rs' k)
              | None => S (e01h_find_base rs' k) end
end.
End rdst.

(* the carried cells (the 13 saves, the four float saves, the flag-pointer word) survive a change of memory that
   keeps [S - 0x88, S) and [F + 0x3f8, F + 0x400) *)
Section kept. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma e01h_kept_keep : forall (hx : hqu_hcx rsegs) pos e (W : world rsegs) mem mem' regs regs',
(forall a, e_S e - 0x88 <= a < e_S e -> aview rsegs (w_H W) mem' a = aview rsegs (w_H W) mem a) ->
(forall a, e_F e + 0x3f8 <= a < e_F e + 0x400 -> aview rsegs (w_H W) mem' a = aview rsegs (w_H W) mem a) ->
hqu_kept rsegs hx pos e W mem regs -> hqu_kept rsegs hx pos e W mem' regs'.
Proof.
intros hx pos e W mem mem' regs regs' KS KF Hk. unfold hqu_kept, hqu_fsaves in *.
destruct Hk as [Hc (v0 & v1 & v2 & v3 & F0 & F1 & F2 & F3)].
split.
- rewrite Forall_forall in *. intros f Hf. pose proof (Hc f Hf) as Hf'.
  unfold hqu_cells in Hf. apply in_app_or in Hf. destruct Hf as [Hf | [<- | []]].
  + unfold hqu_saves_L in Hf. apply in_map_iff in Hf as (j & <- & Hj). apply in_seq in Hj.
    cbn [fst snd hd_at hd_xv] in *.
    apply (val_mem_kept rsegs (w_H W) (w_H W) mem mem'); [|exact Hf'].
    intros k Hk. cbn in Hk. apply KS. lia.
  + cbn [fst snd hd_at hd_xv] in *.
    apply (val_mem_kept rsegs (w_H W) (w_H W) mem mem'); [|exact Hf'].
    intros k Hk. cbn in Hk. apply KF. unfold HQU_FLAG. lia.
- exists v0, v1, v2, v3. cbn [hd_at hd_xv] in *.
  split; [|split; [|split]];
    (apply (val_mem_kept rsegs (w_H W) (w_H W) mem mem'); [|assumption];
     intros k Hk; cbn in Hk; apply KS; lia).
Qed.
End kept.

(* ======================================== the run ========================================
   From 0x80cc4, after the frame call: a0 = F, s1 = sp = R, s4 = n, s11 = K. *)
Definition e01h_extra (F : Z) : list word := [w64 (shadow_addr F)].
Definition e01h_rs : smem := [
  YP09.mkRegion (Some 9%nat) 0x170 0x178 0x170 0x178 [];
  YP09.mkRegion (Some 10%nat) 0 24 0 24 [];
  YP09.mkRegion (Some 32%nat) 0 116 0 116 [] ].
Definition e01h_facts : facts :=
  mkFacts [ (10%nat, mkAF 4096 (2 ^ 47) 5); (20%nat, mkAF 0 (2 ^ 26 - 1) 0) ] [] [].
Definition e01h_ss : sstate := mkSS E01U_SM4_RA sr_atoms e01h_rs None e01h_facts.
(* the write windows of the run's regions *)
Definition e01h_win (R F a : Z) : Prop :=
(R + 0x170 <= a < R + 0x178) \/ (F <= a < F + 24) \/ (shadow_addr F <= a < shadow_addr F + 116).

Section e. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Lemma e01h_entry : forall (W : world rsegs) regs mem R F n,
getr regs 9 = w64 R -> getr regs 10 = w64 F -> getr regs 20 = w64 n ->
0 <= R -> R + 0x178 <= 2 ^ 64 -> 4096 <= F -> F + 1024 <= 2 ^ 47 -> F mod 32 = 0 -> 0 <= n < 2 ^ 26 ->
(forall a, R + 0x170 <= a < R + 0x178 -> apresent (w_H W) mem a) ->
(forall a, F <= a < F + 24 -> apresent (w_H W) mem a) ->
(forall i, 0 <= i < 116 -> apresent (w_H W) mem (shadow_addr F + i)) ->
zpairwise_disjoint [(R + 0x170, R + 0x178); (F, F + 24); (shadow_addr F, shadow_addr F + 116)] ->
st_ok rsegs (Ereg regs (e01h_extra F)) e01h_ss
  (restrict (w_H W) (mkst regs (Z_to_bv 64 E01U_SM4_RA) mem (seg_rom rsegs))).
Proof.
intros W regs mem R F n H9 H10 H20 HR0 HR1 HF0 HF1 HF32 Hn PR PF PSh Hdisj.
rewrite restrict_mkst_fx.
set (E := Ereg regs (e01h_extra F)).
assert (U9 : bv_unsigned (ew E 9) = R).
{ subst E. rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl), H9. unfold w64. apply unsigned_lit_small. lia. }
assert (U10 : bv_unsigned (ew E 10) = F).
{ subst E. rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl), H10. unfold w64. apply unsigned_lit_small. lia. }
assert (U20 : bv_unsigned (ew E 20) = n).
{ subst E. rewrite (ew_Ereg_nat regs _ 20 20%bv eq_refl), H20. unfold w64. apply unsigned_lit_small. lia. }
assert (HshF : 0 <= shadow_addr F < 2 ^ 45).
{ revert HF0 HF1. clear. intros. unfold shadow_addr, SHADOW_OFF.
  split; [apply Z.add_nonneg_nonneg; [lia | apply Z.div_pos; lia]|].
  assert (F / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia). lia. }
assert (U32 : bv_unsigned (ew E 32) = shadow_addr F).
{ subst E. rewrite (ew_Ereg_extra regs _ 0). cbn [nth e01h_extra]. unfold w64. apply unsigned_lit_small. lia. }
unfold e01h_ss. apply (entry_st_ok_full rsegs); change (Ereg regs (e01h_extra F)) with E.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- unfold e01h_rs. repeat apply Forall_cons; try apply Forall_nil;
  unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  + rewrite U9. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable rsegs). apply PR. lia.
  + rewrite U10. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable rsegs). apply PF. lia.
  + rewrite U32. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable rsegs). apply PSh. lia.
- apply pairwise_disjoint_of_extents.
  unfold e01h_rs, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U10, U32.
  rewrite !Z.add_0_r. exact Hdisj.
- split; [|split; [exact I | exact I]]. cbn [e01h_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite U10, U20. change (2 ^ 5) with 32. rewrite Z.pow_0_r, Z.mod_1_r. repeat split; lia.
Qed.
End e.

(* the windows of a run lie in e01h_win: every region of the state is one of the three *)
Ltac e01h_winT U9 U10 U32 :=
  let a := fresh "a" in let r := fresh "r" in let Hin := fresh "Hin" in let Ha := fresh "Ha" in
  intros a (r & Hin & Ha);
  lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end;
  repeat (destruct Hin as [<- | Hin];
    [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
      first [ rewrite U9 in Ha | rewrite U10 in Ha | rewrite U32 in Ha | idtac ];
      unfold e01h_win; revert Ha; clear; intros Ha; lia | ]);
  destruct Hin.
(* compose a run's keep with the keep so far, from the memory after the frame call (KP) *)
Ltac e01h_keep HFr KP R F U9 U10 U32 :=
  lazymatch type of HFr with frame_of ?E ?rs (mrestrict ?H ?m0) (mrestrict _ ?m1) =>
  lazymatch type of KP with forall a, _ -> _ -> aview _ _ ?mx a = aview _ _ ?mb a =>
  let K := fresh "K" in let K2 := fresh "K" in
  assert (K : forall a, 0 <= a < 2 ^ 64 -> ~ e01h_win R F a -> aview rsegs H m1 a = aview rsegs H m0 a)
    by (apply (e01h_keep_frame E rs H m0 m1 _ HFr); e01h_winT U9 U10 U32);
  assert (K2 : forall a, 0 <= a < 2 ^ 64 -> ~ e01h_win R F a -> aview rsegs H m1 a = aview rsegs H mb a)
    by (let a := fresh "a" in let Ha := fresh "Ha" in let Hn := fresh "Hn" in
        intros a Ha Hn; rewrite (K a Ha Hn); exact (KP a Ha Hn));
  clear K KP; rename K2 into KP end end.
(* the write windows: the real-frame cell (the stack window), the frame's header and its shadow (the frame the
   journal owns) *)
Ltac e01h_awr R S0 F pos U9 U10 U32 HFly HRr HSTK HASTK :=
  lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
  let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0 bc ly own) end;
  repeat first
  [ apply awr_ok_nil
  | apply awr_ok_cons_ro; [cbn; clear; lia|]
  | eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (R - S0));
    [reflexivity | rewrite U9; clear; lia
    | cbn; revert HRr HSTK HASTK; clear; intros; rewrite HASTK in HSTK; lia | cbn; revert HRr; clear; lia |]
  | eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 10%nat F); [reflexivity | exact U10 | |];
    [ cbn [YP09.r_wlo YP09.r_whi]; let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
      right; right; right; exists HQU_CID, pos; split; [left; reflexivity|];
      left; unfold in_zr; cbn [fst snd]; rewrite HFly; change (fs_frame_bytes HQU_CID) with 1024;
      revert Ha; clear; lia |]
  | eapply (HPgSteps.awr_ok_cons_fshadow _ _ _ _ _ _ _ _ _ _ 32%nat HQU_CID pos);
    [ reflexivity | rewrite U32, HFly; reflexivity | left; reflexivity
    | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; change (fs_frame_bytes HQU_CID / 8) with 128; lia |] ].
Ltac e01h_nin := let H := fresh "H" in intros H; repeat (destruct H as [H|H]; [discriminate H|]); destruct H.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variables RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK : Z.
Hypothesis HSTK : 0x230 + ASTACK <= LLVMF_STK.

Theorem e01u_hdr_ok : e01u_hdr_stmt B RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK.
Proof.
intros hx pos e ly S W regs mem md HB HFR.
pose proof HPgSteps.img_wx as Hwx. pose proof HPgSteps.img_segs_low as Hsegs.
pose proof (AR_laws_ok rsegs B) as LAWS.
destruct HFR as (HJ & Eab & HGeo & R2 & R3 & R4 & R8 & R9 & R10 & R18 & R20 & R27 & _ & HK).
pose proof HB as (HPRE & _ & _ & _ & Hpn & _ & _ & Hfr0 & _).
pose proof HPRE as (_ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (YM05.alloc_ceiling_val) as Hceilv.
assert (HASTK : ASTACK = 16384) by reflexivity.
pose proof HGeo as (GS & GR & GF).
unfold hqu_j in HJ.
pose proof HJ as (HAR & Hly & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & HJpres & _).
pose proof Hly as (_ & _ & _ & _ & _ & HlyF & _).
set (S0 := spZ (hu_regs rsegs hx)) in *.
set (R := e_R e) in *. set (F := e_F e) in *.
assert (HFly : frame_addr ly HQU_CID pos = F) by (rewrite GF; unfold frame_addr; rewrite HlyF; reflexivity).
assert (Hfin : In (HQU_CID, pos) (frames S)) by (rewrite Hfrs; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ HQU_CID pos HAR Hfin) as (HF32 & HFapp & HFpres & HFSpres).
destruct (frames_bounds rsegs B LAWS _ _ _ _ _ HQU_CID pos HAR Hfin) as (HF4096 & HFceil & _).
rewrite HFly in HF32, HFapp, HFpres, HFSpres, HF4096, HFceil.
change (fs_frame_bytes HQU_CID) with 1024 in *. change (1024 / 8) with 128 in HFSpres.
(* the geometry: R = 32 ((S - 0x220) / 32), so S - 0x23f <= R <= S - 0x220 *)
assert (HRr : S0 - 0x23f <= R <= S0 - 0x220).
{ rewrite GR. unfold HQU_RSZ. rewrite GS. pose proof (Z.div_mod (S0 - 0x220) 32 ltac:(lia)) as D.
  pose proof (Z.mod_pos_bound (S0 - 0x220) 32 ltac:(lia)) as M. lia. }
assert (Hn26 : 0 <= hu_n rsegs hx < 2 ^ 26) by (revert Hpn; clear; intros [[-> _] | [Hn' _]]; lia).
assert (HshF : 0 <= shadow_addr F < 2 ^ 45).
{ revert HF4096 HFceil Hceilv. clear. intros. unfold shadow_addr, SHADOW_OFF.
  split; [apply Z.add_nonneg_nonneg; [lia | apply Z.div_pos; lia]|].
  assert (F / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia). lia. }
assert (HF8 : F = 8 * (F / 8) + F mod 8 /\ 0 <= F mod 8 < 8) by (split; [apply Z.div_mod; lia | apply Z.mod_pos_bound; lia]).
assert (HDJ : zpairwise_disjoint [(R + 0x170, R + 0x178); (F, F + 24); (shadow_addr F, shadow_addr F + 116)]).
{ cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj, shadow_addr, SHADOW_OFF. cbn [fst snd].
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp.
  revert HF8 HFapp HFceil Hceilv HRr Hceil Hslo Hstk0 HSTK HASTK. clear. intros. rewrite HASTK in HSTK.
  repeat split; lia. }
pose proof (e01h_entry W regs mem R F (hu_n rsegs hx) R9 R10 R20
  ltac:(revert HRr Hceil Hslo Hstk0 Hceilv; clear; lia) ltac:(revert HRr Hshi H47; clear; lia)
  HF4096 ltac:(revert HFceil Hceilv; clear; lia) HF32 Hn26
  ltac:(intros a Ha; apply HJpres; revert Ha HRr HSTK HASTK; clear; intros; rewrite HASTK in HSTK; lia)
  ltac:(intros a Ha; apply (proj1 (HFpres a ltac:(revert Ha; clear; lia))))
  ltac:(intros i Hi; apply (proj1 (HFSpres i ltac:(revert Hi; clear; lia))))
  HDJ) as HS0.
clear HDJ.
(* the alias of the frame's shadow base (F >> 3) + K *)
assert (E10 : ew (Ereg regs (e01h_extra F)) 10 = Z_to_bv 64 F)
  by (rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact R10).
assert (E27 : ew (Ereg regs (e01h_extra F)) 27 = Z_to_bv 64 SHADOW_OFF)
  by (rewrite (ew_Ereg_nat regs _ 27 27%bv eq_refl); exact R27).
assert (E32 : ew (Ereg regs (e01h_extra F)) 32 = Z_to_bv 64 (SHADOW_OFF + F / 8))
  by (rewrite (ew_Ereg_extra regs _ 0); reflexivity).
pose proof (shadow_decl_ok (Ereg regs (e01h_extra F)) 10 27 32 F SHADOW_OFF E10
  ltac:(revert HF4096 HFceil Hceilv; clear; lia) E27 E32) as DAL.
pose proof (st_ok_add_alias rsegs _ _ _ (SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 0) (SLit 3)) (SOff 27 0)) (SOff 32 0) HS0 DAL) as HS.
clear HS0.
assert (U9 : bv_unsigned (ew (Ereg regs (e01h_extra F)) 9) = R).
{ rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl), R9. unfold w64. apply unsigned_lit_small.
  revert HRr Hceil Hslo Hstk0 Hshi H47 Hceilv; clear; lia. }
assert (U10 : bv_unsigned (ew (Ereg regs (e01h_extra F)) 10) = F).
{ rewrite E10. apply unsigned_lit_small. revert HF4096 HFceil Hceilv; clear; lia. }
assert (U20 : bv_unsigned (ew (Ereg regs (e01h_extra F)) 20) = hu_n rsegs hx).
{ rewrite (ew_Ereg_nat regs _ 20 20%bv eq_refl), R20. unfold w64. apply unsigned_lit_small. revert Hn26; clear; lia. }
assert (U32 : bv_unsigned (ew (Ereg regs (e01h_extra F)) 32) = shadow_addr F).
{ rewrite (ew_Ereg_extra regs _ 0). cbn [nth e01h_extra]. unfold w64. apply unsigned_lit_small. revert HshF; clear; lia. }
assert (KP : forall a, 0 <= a < 2 ^ 64 -> ~ e01h_win R F a -> aview rsegs (w_H W) mem a = aview rsegs (w_H W) mem a)
  by reflexivity.
(* ---- the run: 0x80cc4 .. the size test's `beqz a3` 0x80f08 ---- *)
unfold cfg_at. change (w64 E01U_SM4_RA) with (Z_to_bv 64 E01U_SM4_RA).
aj_run_to E01U_TBL_ok HS HJ E01U_HDR. { e01h_awr R S0 F pos U9 U10 U32 HFly HRr HSTK HASTK. }
e01h_keep HFr KP R F U9 U10 U32.
rename ms into ms4, HS into HS4, HJ into HJ4, HF into HF4, HFr into HFr4, HG into HG4.
lazymatch goal with |- SRr _ ?Wg (mkCfg ?msF ?mdF) _ =>
  lazymatch type of HS4 with st_ok _ ?Ev ?ssv _ =>
  apply (SRr_sym_branch rsegs Wg Ev ssv msF mdF _ BC_EQ (SAlu ALU_SRL (SOff 20 0) (SLit 26)) (SLit 0) HS4) end end;
intros Hc HS5; clear HS4.
2:{ (* not taken: n >> 26 <> 0, impossible *)
  exfalso. rewrite branch_eq_U, U_SAlu in Hc. cbn [zalu_raw] in Hc.
  rewrite (U_atom _ 20 (hu_n rsegs hx)) in Hc;
    [| rewrite (ew_Ereg_nat regs _ 20 20%bv eq_refl); exact R20 | revert Hn26; clear; lia].
  rewrite !U_SLit in Hc. change (Z.land (zcanon 26) 63) with 26 in Hc. change (zcanon 0) with 0 in Hc.
  rewrite Z.shiftr_div_pow2 in Hc by lia. rewrite (Z.div_small (hu_n rsegs hx) (2 ^ 26)) in Hc by (revert Hn26; clear; lia).
  vm_compute in Hc. discriminate Hc. }
(* taken: 0x80f08 -> 0x80f10 *)
aj_run_to E01U_TBL_ok HS5 HJ4 E01U_HDR. { e01h_awr R S0 F pos U9 U10 U32 HFly HRr HSTK HASTK. }
e01h_keep HFr KP R F U9 U10 U32.
rename ms into ms6, HS5 into HS6, HJ4 into HJ6, HF into HF6, HFr into HFr6, HG into HG6.
(* ---- the last state, pc 0x80f10 ---- *)
apply SRr_ret. unfold e01u_at_hdr.
exists pos, e, ly, S, (ms_regs ms6), (ms_mem ms6). eexists.
split; [rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ ms6 HS6 eq_refl) at 1; reflexivity|].
pose proof (HPgSteps.regs_kept_of_st_ok rsegs _ _ ms6 regs (e01h_extra F) (w_H W)
  [10; 11; 12; 13; 14; 15; 19; 21; 23]%bv HS6 (env_agree_refl 32 _) ltac:(vm_compute; reflexivity)) as KR.
assert (D10 : sv_denot (Ereg regs (e01h_extra F)) (SOff 10 0) = w64 F).
{ apply bv_eq. rewrite denot_SOff, Z.add_0_r, U10. unfold w64. rewrite unsigned_lit_small by (revert HF4096 HFceil Hceilv; clear; lia).
  apply zcanon_id. unfold M64. revert HF4096 HFceil Hceilv; clear; lia. }
assert (D32 : sv_denot (Ereg regs (e01h_extra F)) (SOff 32 0) = w64 (shadow_addr F)).
{ apply bv_eq. rewrite denot_SOff, Z.add_0_r, U32. unfold w64. rewrite unsigned_lit_small by (revert HshF; clear; lia).
  apply zcanon_id. unfold M64. revert HshF; clear; lia. }
unfold e01u_hdr_facts.
split; [unfold hqu_j; exact HJ6|].
split; [exact Eab|].
split; [exact HGeo|].
split; [rewrite KR; [exact R2 | vm_compute; discriminate | vm_compute; e01h_nin]|].
split; [rewrite KR; [exact R3 | vm_compute; discriminate | vm_compute; e01h_nin]|].
split; [rewrite KR; [exact R4 | vm_compute; discriminate | vm_compute; e01h_nin]|].
split; [rewrite KR; [exact R8 | vm_compute; discriminate | vm_compute; e01h_nin]|].
split; [rewrite KR; [exact R9 | vm_compute; discriminate | vm_compute; e01h_nin]|].
split; [rewrite KR; [exact R18 | vm_compute; discriminate | vm_compute; e01h_nin]|].
split.
{ rewrite (st_ok_restrict_reg rsegs (w_H W) _ _ ms6 _ HS6).
  lazymatch type of HS6 with st_ok _ _ ?ssf _ =>
    let x := eval vm_compute in (sr_get (ss_regs ssf) (19%bv : bv 5)) in
    change (sr_get (ss_regs ssf) (19%bv : bv 5)) with x end.
  first [exact D32 | rewrite DAL; exact D32]. }
split; [rewrite KR; [exact R20 | vm_compute; discriminate | vm_compute; e01h_nin]|].
split.
{ rewrite (st_ok_restrict_reg rsegs (w_H W) _ _ ms6 _ HS6).
  lazymatch type of HS6 with st_ok _ _ ?ssf _ =>
    let x := eval vm_compute in (sr_get (ss_regs ssf) (21%bv : bv 5)) in
    change (sr_get (ss_regs ssf) (21%bv : bv 5)) with x end.
  exact D10. }
split.
{ rewrite (st_ok_restrict_reg rsegs (w_H W) _ _ ms6 _ HS6).
  lazymatch type of HS6 with st_ok _ _ ?ssf _ =>
    let x := eval vm_compute in (sr_get (ss_regs ssf) (23%bv : bv 5)) in
    change (sr_get (ss_regs ssf) (23%bv : bv 5)) with x end.
  exact D10. }
split; [rewrite KR; [exact R27 | vm_compute; discriminate | vm_compute; e01h_nin]|].
split.
{ (* the frame's 116 shadow bytes, from the shadow region's chunks *)
  lazymatch type of HS6 with st_ok _ ?Ev ?ss _ =>
  let i32 := eval vm_compute in (e01h_find_base (ss_mem ss) 32) in
  let r32 := eval vm_compute in (nth_error (ss_mem ss) i32) in
  lazymatch r32 with Some ?rg32 =>
  pose proof (HPgSteps.st_ok_region_at _ _ _ i32 rg32 HS6 ltac:(vm_compute; reflexivity)) as RG32 end end.
  change (ms_mem (restrict (w_H W) ms6)) with (mrestrict (w_H W) (ms_mem ms6)) in RG32.
  apply (e01h_fsh_of_region _ _ _ 32 F _ _ _ _ _ headamp_B_shA RG32 U32). vm_compute. reflexivity. }
(* the carried cells lie outside the run's windows *)
apply (e01h_kept_keep hx pos e W mem (ms_mem ms6) regs (ms_regs ms6)); [| |exact HK].
- intros a Ha. fold S0 R F in Ha |- *. rewrite GS in Ha. fold S0 in Ha. apply KP.
  + revert Ha Hceil Hslo Hstk0 Hshi H47 Hceilv; clear; intros; lia.
  + unfold e01h_win. unfold shadow_addr, SHADOW_OFF in HshF |- *.
    revert Ha HRr Hceil Hslo Hstk0 HSTK HASTK Hceilv HFceil HshF. clear. intros. rewrite HASTK in HSTK. lia.
- intros a Ha. fold F in Ha |- *. apply KP.
  + revert Ha HF4096 HFceil Hceilv; clear; intros; lia.
  + unfold e01h_win. pose proof (Z.div_mod F 8 ltac:(lia)) as DF.
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp. unfold shadow_addr, SHADOW_OFF.
    revert Ha DF HF8 HRr Hceil Hslo Hstk0 HSTK HASTK Hceilv HFceil HFapp HF4096. clear. intros. rewrite HASTK in HSTK. lia.
Qed.
End b.

Print Assumptions e01u_hdr_ok.
About e01u_hdr_ok.
