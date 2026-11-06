(* Modified by Theorem Labs, 2026-10: the helper lemmas and Ltacs (keep_frame, reg_atom, reg_off, the frame-shadow
   reader, the window and keep Ltacs, the write-window Ltac) are adapted from proofs/reac-pw/fuzz_role/lib/A/RPgE01.v
   (fuzz_role's walk of the same harness, its run P2, uncommitted working copy over a1f54c45fc22); renamed e01h_,
   moved to headamp's class-4 frame, its slot R+0x138, its 80 frame shadow bytes and HPgE01D's cut states. *)
(* reac-pw/fuzz_headamp image A (fuzz_headamp.asan, pinned sha256
   f3e0669d2819724922df0556b11c2dcd22d1e16fe7e0fe1535ce784b34436c47; every address below is measured on the
   unstripped twin b5f352154c54a97c66fd92dfa228e8a854498f6cd313dba0107900546b043f9a, whose loaded sections other than
   .note.gnu.build-id are byte-equal to the pin's): part 2 of segment E01 of the walk of LLVMFuzzerTestOneInput (lib/A/HPgE01D.v
   e01_hdr_stmt), from the return of the class-4 frame call 0x80c40 (RA_SM4) to the size test's exit E01_HDR
   0x80dfc. Proves no function (kind: segment lemma of LLVMFuzzerTestOneInput's walk: segment E01, part 2 of 4).

   THE CODE (capstone over the unstripped twin; HPgE01D.v E01_TBL):
     0x80c40 .. 0x80c50  mv s6,a0; j 0x80c4c; mv s10,s6; bnez s6 (taken: the frame F >= 4096, so the real-stack
                         arm 0x80c54 .. 0x80c6c and its probe loop are in no run)
     0x80c70             sd s10,0x138(s1)                          (the slot R+0x138 := F)
     0x80c74 .. 0x80ca4  the header: F[0] = 0x41b58ab3, F[8] = 0x19e98, F[16] = 0x80bc0
     0x80c80, 0x80cac    srli s3,s10,3; add s3,s3,s7               (s3 = (F >> 3) + K = shadow_addr F)
     0x80cb0 .. 0x80df0  the 80 frame shadow stores (headamp_A_shA); 0x80cc0 srli a3,s2,0x1a (a3 = n >> 26)
     0x80df4             beqz a3 (taken: n < 2 ^ 26; the `j` 0x80df8 to the retirement join is in no run)
   THE ROUTE (the engine's, as fuzz_role's run P2): one engine state at 0x80c40 over the registers and one extra
   atom 32 = shadow_addr F, with the alias the code's `srli; add` forms ((F >> 3) + K = atom 32), the facts
   F in [4096, 2^47] 32-aligned and n in [0, 2^26 - 1], and three regions: the slot [R+0x138, R+0x140) (base s1,
   atom 9), the header [F, F+24) (base a0, atom 10) and the 80 shadow bytes (base atom 32). The run stops at the
   undecided `beqz a3`; YA0o.SRr_sym_branch splits it, the not-taken side is false by n < 2^26, the taken side
   runs one step to 0x80dfc. The slot is in the journal's stack window; the header and the shadow bytes are the
   held frame's (in_frames of own). The carried cells (the saves [S-0x68, S), the float saves [S-0x80, S-0x68),
   the flag word [F+0x3f8, F+0x400)) lie outside the three write windows. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05 YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Cursor Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import Img0 HPgBase HPgCSpec HPgImgA HPgSegM HPgCalls.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require HPgSteps.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgE01D.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ================================ reading a run's last state ================================ *)
Section rdst. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
(* a register the state holds as an entry atom *)
Lemma e01h_reg_atom : forall H E ss ms regs0 extra (r : bv 5) n,
st_ok rsegs E ss (restrict H ms) -> E = Ereg regs0 extra -> sr_get (ss_regs ss) r = SOff n 0 -> (n < 32)%nat ->
getr (ms_regs ms) r = getr regs0 (Z_to_bv 5 (Z.of_nat n)).
Proof.
intros H E ss ms regs0 extra r n HS HE Hsr Hn.
rewrite (st_ok_restrict_reg rsegs H E ss ms r HS), Hsr. apply bv_eq. rewrite denot_SOff, Z.add_0_r, HE.
rewrite (ew_Ereg_nat regs0 extra n (Z_to_bv 5 (Z.of_nat n))).
- apply zcanon_id. pose proof (bv_unsigned_in_range _ (getr regs0 (Z_to_bv 5 (Z.of_nat n)))) as Hb.
  change (bv_modulus 64) with (2 ^ 64) in Hb. unfold M64. lia.
- rewrite Z_to_bv_unsigned. symmetry. apply bv_wrap_small. change (bv_modulus 5) with 32. lia.
Qed.
(* a register the state holds as an atom plus an offset, at the value the atom gives *)
Lemma e01h_reg_off : forall H E ss ms (r : bv 5) n c v,
st_ok rsegs E ss (restrict H ms) -> sr_get (ss_regs ss) r = SOff n c ->
bv_unsigned (ew E n) + c = v -> getr (ms_regs ms) r = w64 v.
Proof.
intros H E ss ms r n c v HS Hsr Hu.
rewrite (st_ok_restrict_reg rsegs H E ss ms r HS), Hsr, denot_lit_U, U_SOff, Hu. unfold w64. apply Z_to_bv64_canon.
Qed.
(* the frame's shadow bytes, from the one-byte literal chunks the stores leave in their region *)
Definition e01h_sh_ok (pat : list Z) (i : nat) (c : YP09.chunk) : bool :=
match c with
| YP09.mkChunk off (CVal w (SLit z)) => (off =? Z.of_nat i) && N.eqb w 1 && (z mod 256 =? nth i pat 0)
| _ => false
end.
Lemma e01h_sh_ok_spec : forall pat i c, e01h_sh_ok pat i c = true ->
exists z, c = YP09.mkChunk (Z.of_nat i) (CVal 1 (SLit z)) /\ z mod 256 = nth i pat 0.
Proof.
intros pat i [off v] H. destruct v as [w s | | |]; try discriminate. destruct s; try discriminate.
cbn [e01h_sh_ok] in H.
apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
apply Z.eqb_eq in H1. apply N.eqb_eq in H2. apply Z.eqb_eq in H3. subst. eexists. split; [reflexivity | exact H3].
Qed.
Lemma e01h_fsh_of_region : forall E H mem (k : nat) F lo hi wlo whi cs pat,
region_ok rsegs E (mrestrict H mem) (YP09.mkRegion (Some k) lo hi wlo whi cs) ->
bv_unsigned (ew E k) = shadow_addr F ->
forallb (fun i => existsb (e01h_sh_ok pat i) cs) (seq 0 (length pat)) = true ->
hd_fsh rsegs H mem F pat.
Proof.
intros E H mem k F lo hi wlo whi cs pat (_ & _ & _ & Hcs) Hb Hck i Hi.
cbn [YP09.r_base YP09.r_chunks base_val] in Hcs. rewrite Hb in Hcs.
assert (Hin : In (Z.to_nat i) (seq 0 (length pat))) by (apply in_seq; lia).
pose proof (proj1 (forallb_forall _ _) Hck _ Hin) as Hx. apply existsb_exists in Hx as (c & Hc & Hok).
apply e01h_sh_ok_spec in Hok as (z & -> & Hz).
pose proof (HPgSteps.fsh_byte_of_region_mod E (mrestrict H mem) (shadow_addr F) cs (Z.of_nat (Z.to_nat i)) z Hcs Hc)
  as Hb1.
rewrite Z2Nat.id in Hb1 by lia. unfold aview. rewrite Hb1, Hz. reflexivity.
Qed.
(* a run keeps every byte outside the write windows of its regions *)
Lemma e01h_keep_frame : forall E rs H (m m' : word -> option byte) (P : Z -> Prop),
frame_of E rs (mrestrict H m) (mrestrict H m') -> (forall a, in_wrange E rs a -> P a) ->
forall a, 0 <= a < 2 ^ 64 -> ~ P a -> aview rsegs H m' a = aview rsegs H m a.
Proof.
intros E rs H m m' P HF HW a Ha Hz. unfold aview, mbyte.
rewrite (HF (Z_to_bv 64 a)); [reflexivity|]. rewrite unsigned_lit_small by exact Ha. intros X. exact (Hz (HW a X)).
Qed.
(* the index of the region whose base is atom k *)
Fixpoint e01h_find_base (rs : smem) (k : nat) : nat :=
match rs with
| [] => O
| r :: rs' => match YP09.r_base r with Some k' => if Nat.eqb k k' then O else S (e01h_find_base rs' k)
              | None => S (e01h_find_base rs' k) end
end.
End rdst.

(* ======================================== the run ========================================
   From 0x80c40, after the frame call: a0 = F, s1 = R, s2 = n, s7 = K. The regions: the slot [R+0x138, R+0x140)
   (s1, atom 9), the frame's header words [F, F+24) (a0, atom 10) and its 80 shadow bytes from (F >> 3) + K
   (atom 32, the one extra atom, with the alias the code's `srli s3,s10,3` / `add s3,s3,s7` forms). *)
Definition e01h_extra (F : Z) : list word := [w64 (shadow_addr F)].
Definition e01h_rs : smem := [
  YP09.mkRegion (Some 9%nat) 0x138 0x140 0x138 0x140 [];
  YP09.mkRegion (Some 10%nat) 0 24 0 24 [];
  YP09.mkRegion (Some 32%nat) 0 80 0 80 [] ].
Definition e01h_facts : facts :=
  mkFacts [ (10%nat, mkAF 4096 (2 ^ 47) 5); (18%nat, mkAF 0 (2 ^ 26 - 1) 0) ] [] [].
Definition e01h_ss : sstate := mkSS RA_SM4 sr_atoms e01h_rs None e01h_facts.
(* the run's write windows: the slot, the frame's header, its 80 shadow bytes *)
Definition e01h_win (R F a : Z) : Prop :=
(R + 0x138 <= a < R + 0x140) \/ (F <= a < F + 24) \/ (shadow_addr F <= a < shadow_addr F + 80).

Section e. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Lemma e01h_entry : forall (W : world rsegs) regs mem R F n,
getr regs 9 = w64 R -> getr regs 10 = w64 F -> getr regs 18 = w64 n ->
0 <= R -> R + 0x140 <= 2 ^ 64 -> 4096 <= F -> F <= 2 ^ 47 -> F mod 32 = 0 -> 0 <= n < 2 ^ 26 ->
0 <= shadow_addr F -> shadow_addr F + 80 <= 2 ^ 64 ->
(forall a, R + 0x138 <= a < R + 0x140 -> apresent (w_H W) mem a) ->
(forall a, F <= a < F + 24 -> apresent (w_H W) mem a) ->
(forall i, 0 <= i < 80 -> apresent (w_H W) mem (shadow_addr F + i)) ->
zpairwise_disjoint [(R + 0x138, R + 0x140); (F, F + 24); (shadow_addr F, shadow_addr F + 80)] ->
st_ok rsegs (Ereg regs (e01h_extra F)) e01h_ss
  (restrict (w_H W) (mkst regs (Z_to_bv 64 RA_SM4) mem (seg_rom rsegs))).
Proof.
intros W regs mem R F n H9 H10 H18 HR0 HR1 HF0 HF1 HF32 Hn Hs0 Hs1 PR PF PSh Hdisj.
rewrite restrict_mkst_fx.
set (E := Ereg regs (e01h_extra F)).
assert (U9 : bv_unsigned (ew E 9) = R).
{ subst E. rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl), H9. unfold w64. apply unsigned_lit_small. lia. }
assert (U10 : bv_unsigned (ew E 10) = F).
{ subst E. rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl), H10. unfold w64. apply unsigned_lit_small. lia. }
assert (U18 : bv_unsigned (ew E 18) = n).
{ subst E. rewrite (ew_Ereg_nat regs _ 18 18%bv eq_refl), H18. unfold w64. apply unsigned_lit_small. lia. }
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
  rewrite U10, U18. change (2 ^ 5) with 32. rewrite Z.pow_0_r, Z.mod_1_r. repeat split; lia.
Qed.
End e.

(* every region of the state is one of the run's three: its write window lies in e01h_win *)
Ltac e01h_win2 U9 U10 U32 :=
  let a := fresh "a" in let r := fresh "r" in let Hin := fresh "Hin" in let Ha := fresh "Ha" in
  intros a (r & Hin & Ha);
  lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end;
  repeat (destruct Hin as [<- | Hin];
    [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
      first [ rewrite U9 in Ha | rewrite U10 in Ha | rewrite U32 in Ha | idtac ];
      unfold e01h_win; revert Ha; clear; intros Ha; lia | ]);
  destruct Hin.
(* compose a run's keep with the keep so far (KP: from the memory at 0x80c40) *)
Ltac e01h_keep2 HFr KP R F U9 U10 U32 :=
  lazymatch type of HFr with frame_of ?E ?rs (mrestrict ?H ?m0) (mrestrict _ ?m1) =>
  lazymatch type of KP with forall a, _ -> _ -> aview _ _ ?mx a = aview _ _ ?mb a =>
  let K := fresh "K" in let K2 := fresh "K" in
  assert (K : forall a, 0 <= a < 2 ^ 64 -> ~ e01h_win R F a -> aview rsegs H m1 a = aview rsegs H m0 a)
    by (apply (e01h_keep_frame E rs H m0 m1 _ HFr); e01h_win2 U9 U10 U32);
  assert (K2 : forall a, 0 <= a < 2 ^ 64 -> ~ e01h_win R F a -> aview rsegs H m1 a = aview rsegs H mb a)
    by (let a := fresh "a" in let Ha := fresh "Ha" in let Hn := fresh "Hn" in
        intros a Ha Hn; rewrite (K a Ha Hn); exact (KP a Ha Hn));
  clear K KP; rename K2 into KP end end.
(* the write windows of the run's regions: the slot (the journal's stack window), the frame's header and its shadow
   (the frame the journal owns, class 4: 1024 bytes, 128 shadow bytes) *)
Ltac e01h_awr R S0 F pos U9 U10 U32 HFeq HRr HSTK HASTK :=
  lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
  let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0 bc ly own) end;
  repeat first
  [ apply awr_ok_nil
  | apply awr_ok_cons_ro; [cbn; clear; lia|]
  | eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (R - S0));
    [ reflexivity | rewrite U9; clear; lia
    | cbn [YP09.r_wlo]; revert HRr HSTK HASTK; clear; intros; rewrite HASTK in HSTK; lia
    | cbn [YP09.r_whi]; revert HRr; clear; intros; lia | ]
  | eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 10%nat F); [reflexivity | exact U10 | |];
    [ cbn [YP09.r_wlo YP09.r_whi]; let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
      right; right; right; exists 4, pos; split; [left; reflexivity|];
      left; unfold in_zr; cbn [fst snd]; rewrite HFeq; change (fs_frame_bytes 4) with 1024; revert Ha; clear; lia |]
  | eapply (HPgSteps.awr_ok_cons_fshadow _ _ _ _ _ _ _ _ _ _ 32%nat 4 pos);
    [ reflexivity | rewrite HFeq; exact U32 | left; reflexivity | cbn [YP09.r_wlo]; lia
    | cbn [YP09.r_whi]; change (fs_frame_bytes 4 / 8) with 128; lia | ] ].

Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variables RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK : Z.
Hypothesis HSTK : 0x1f0 + ASTACK <= LLVMF_STK.

Theorem e01_hdr_ok : e01_hdr_stmt B RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK.
Proof.
intros hx pos e ly S W regs mem md HB HFR.
unfold e01_fr_facts in HFR.
destruct HFR as (HJ0 & Eab & HGEO & R2 & R3 & R4 & R8 & R9 & R10 & R18 & R23 & R27 & _ & HK).
pose proof HGEO as (GS & GR & GF).
pose proof HB as (HPRE & _ & _ & _ & Hpn & _).
pose proof HPRE as (_ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
clear HPRE Hstk.
pose proof asan_consts as (C1 & _ & _ & _ & _).
pose proof (AR_laws_ok rsegs B) as LAWS.
pose proof HPgSteps.img_wx as Hwx. pose proof HPgSteps.img_segs_low as Hsegs.
unfold hq_j in HJ0.
assert (HASTK : ASTACK = 16384) by reflexivity.
assert (Hn26 : 0 <= h_n rsegs hx < 2 ^ 26) by (destruct Hpn as [[Hz _] | [Hn' _]]; lia).
clear Hpn.
(* ---- the frame F = frame_addr ly 4 pos: bounds, alignment, presence of its header and shadow ---- *)
assert (Hown : In (HQ_CID, pos) [(HQ_CID, pos)]) by (left; reflexivity).
destruct (hc_frm_low rsegs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HQ_CID pos HJ0 Hown) as (HF4096 & HFceil).
pose proof (hc_frm_align rsegs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HQ_CID pos HJ0 Hown) as HF32.
pose proof (hc_frame_addr_j rsegs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HQ_CID pos HJ0) as HFa.
assert (HFeq : frame_addr ly 4 pos = e_F e) by (rewrite GF; exact HFa).
assert (HFeqC : frame_addr ly HQ_CID pos = e_F e) by exact HFeq.
rewrite HFeqC in HF4096, HFceil, HF32. change (fs_frame_bytes HQ_CID) with 1024 in HFceil.
pose proof HJ0 as (HAR & _ & _ & _ & _ & Hfrs & _).
assert (Hfin : In (4, pos) (frames S)) by (rewrite Hfrs; apply in_app_iff; left; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ 4 pos HAR Hfin) as (_ & HFapp & HFpres & HFSpres).
rewrite HFeq in HFapp, HFpres, HFSpres.
change (fs_frame_bytes 4) with 1024 in HFapp, HFpres, HFSpres. change (1024 / 8) with 128 in HFSpres.
pose proof HJ0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres & _).
assert (HF8 : 8 * (e_F e / 8) <= e_F e < 8 * (e_F e / 8) + 8).
{ pose proof (Z.div_mod (e_F e) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (e_F e) 8 ltac:(lia)). lia. }
(* ---- R = 32 ((S - 0x1e0) / 32) ---- *)
assert (HRr : spZ (h_regs rsegs hx) - 0x1e0 - 31 <= e_R e <= spZ (h_regs rsegs hx) - 0x1e0).
{ rewrite GR, GS. unfold HQ_RSZ.
  pose proof (Z.div_mod (spZ (h_regs rsegs hx) - 0x1e0) 32 ltac:(lia)) as D.
  pose proof (Z.mod_pos_bound (spZ (h_regs rsegs hx) - 0x1e0) 32 ltac:(lia)) as M. lia. }
assert (HDJ : zpairwise_disjoint [(e_R e + 0x138, e_R e + 0x140); (e_F e, e_F e + 24);
  (shadow_addr (e_F e), shadow_addr (e_F e) + 80)]).
{ cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold shadow_addr, SHADOW_OFF.
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp.
  revert HF8 HFapp HFceil C1 HRr Hceil Hslo HSTK HASTK HF4096. clear. intros. rewrite HASTK in HSTK.
  repeat split; lia. }
assert (Hsh : 0 <= shadow_addr (e_F e) /\ shadow_addr (e_F e) + 80 <= 2 ^ 64).
{ unfold shadow_addr, SHADOW_OFF. revert HF8 HFceil C1 HF4096. clear. intros. lia. }
(* ---- the engine state at 0x80c40 and the alias of the frame's shadow base ---- *)
pose proof (e01h_entry W regs mem (e_R e) (e_F e) (h_n rsegs hx) R9 R10 R18
  ltac:(revert HRr Hceil Hslo HSTK HASTK C1; clear; intros; rewrite HASTK in HSTK; lia)
  ltac:(revert HRr Hshi H47; clear; intros; lia)
  HF4096 ltac:(revert HFceil C1; clear; intros; lia) HF32 Hn26 (proj1 Hsh) (proj2 Hsh)
  ltac:(intros a Ha; apply HJpres; revert Ha HRr HSTK HASTK; clear; intros; rewrite HASTK in HSTK; lia)
  ltac:(intros a Ha; apply (proj1 (HFpres a ltac:(lia))))
  ltac:(intros i Hi; apply (proj1 (HFSpres i ltac:(lia))))
  HDJ) as HS0.
clear HDJ.
assert (E10 : ew (Ereg regs (e01h_extra (e_F e))) 10 = Z_to_bv 64 (e_F e))
  by (rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact R10).
assert (E23 : ew (Ereg regs (e01h_extra (e_F e))) 23 = Z_to_bv 64 SHADOW_OFF)
  by (rewrite (ew_Ereg_nat regs _ 23 23%bv eq_refl); exact R23).
assert (E32 : ew (Ereg regs (e01h_extra (e_F e))) 32 = Z_to_bv 64 (SHADOW_OFF + e_F e / 8))
  by exact (ew_Ereg_extra regs (e01h_extra (e_F e)) 0).
pose proof (st_ok_add_alias rsegs _ _ _ (SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 0) (SLit 3)) (SOff 23 0)) (SOff 32 0) HS0
  (shadow_decl_ok _ 10 23 32 (e_F e) SHADOW_OFF E10 ltac:(revert HFceil C1 HF4096; clear; intros; lia) E23 E32))
  as HS.
clear HS0.
assert (U9 : bv_unsigned (ew (Ereg regs (e01h_extra (e_F e))) 9) = e_R e).
{ rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl), R9. unfold w64. apply unsigned_lit_small.
  revert HRr Hceil Hslo Hshi H47 HSTK HASTK C1; clear; intros; rewrite HASTK in HSTK; lia. }
assert (U10 : bv_unsigned (ew (Ereg regs (e01h_extra (e_F e))) 10) = e_F e).
{ rewrite E10. apply unsigned_lit_small. revert HFceil C1 HF4096; clear; intros; lia. }
assert (U32 : bv_unsigned (ew (Ereg regs (e01h_extra (e_F e))) 32) = shadow_addr (e_F e)).
{ rewrite E32. unfold shadow_addr in Hsh |- *. apply unsigned_lit_small. destruct Hsh as [Hsh0 Hsh1].
  revert Hsh0 Hsh1. clear. intros. lia. }
assert (KP : forall a, 0 <= a < 2 ^ 64 -> ~ e01h_win (e_R e) (e_F e) a ->
  aview rsegs (w_H W) mem a = aview rsegs (w_H W) mem a) by (intros; reflexivity).
(* ---- the run 0x80c40 .. the `beqz a3` 0x80df4 ---- *)
unfold cfg_at. change (w64 RA_SM4) with (Z_to_bv 64 RA_SM4).
aj_run_to E01_TBL_ok HS HJ0 E01_HDR.
{ e01h_awr (e_R e) (spZ (h_regs rsegs hx)) (e_F e) pos U9 U10 U32 HFeq HRr HSTK HASTK. }
e01h_keep2 HFr KP (e_R e) (e_F e) U9 U10 U32.
clear HF HFr HG.
(* ---- 0x80df4 `beqz a3` (a3 = n >> 26) ---- *)
lazymatch goal with |- SRr _ ?Wg (mkCfg ?msF ?mdF) _ =>
  lazymatch type of HS with st_ok _ ?Ev ?ssv _ =>
  apply (SRr_sym_branch rsegs Wg Ev ssv msF mdF _ BC_EQ (SAlu ALU_SRL (SOff 18 0) (SLit 26)) (SLit 0) HS) end end;
intros Hc HS1; clear HS.
2:{ (* not taken: n >> 26 <> 0, impossible *)
  exfalso. rewrite branch_eq_U, U_SAlu in Hc. cbn [zalu_raw] in Hc.
  rewrite (U_atom _ 18 (h_n rsegs hx)) in Hc;
    [| rewrite (ew_Ereg_nat regs _ 18 18%bv eq_refl); exact R18 | revert Hn26; clear; lia].
  rewrite !U_SLit in Hc. change (Z.land (zcanon 26) 63) with 26 in Hc.
  rewrite Z.shiftr_div_pow2 in Hc by lia. rewrite (Z.div_small (h_n rsegs hx) (2 ^ 26)) in Hc by (revert Hn26; clear; lia).
  revert Hc. vm_compute. intros Hc. discriminate Hc. }
clear Hc.
(* ---- taken: one step to 0x80dfc ---- *)
aj_run_to E01_TBL_ok HS1 HJ0 E01_HDR.
{ e01h_awr (e_R e) (spZ (h_regs rsegs hx)) (e_F e) pos U9 U10 U32 HFeq HRr HSTK HASTK. }
e01h_keep2 HFr KP (e_R e) (e_F e) U9 U10 U32.
clear HF HFr HG.
rewrite ?wvb_collapse in HJ0.
(* ---- the carried cells lie outside the run's windows ---- *)
assert (NWs : forall a, spZ (h_regs rsegs hx) - 0x80 <= a < spZ (h_regs rsegs hx) ->
  0 <= a < 2 ^ 64 /\ ~ e01h_win (e_R e) (e_F e) a).
{ intros a Ha. unfold e01h_win, shadow_addr, SHADOW_OFF.
  revert Ha HF8 HFceil C1 HRr Hceil Hslo Hshi H47 HSTK HASTK. clear. intros. rewrite HASTK in HSTK.
  split; [lia|]. intros [X|[X|X]]; lia. }
assert (NWfl : forall a, e_F e + 0x3f8 <= a < e_F e + 0x400 -> 0 <= a < 2 ^ 64 /\ ~ e01h_win (e_R e) (e_F e) a).
{ intros a Ha. unfold e01h_win, shadow_addr, SHADOW_OFF.
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp.
  revert Ha HF8 HFapp HFceil C1 HRr Hceil Hslo HSTK HASTK HF4096. clear. intros. rewrite HASTK in HSTK.
  split; [lia|]. intros [X|[X|X]]; lia. }
(* ---- the state at 0x80dfc: e01_hdr_facts ---- *)
lazymatch goal with |- SRr _ _ (mkCfg ?msF ?mdF) _ =>
  apply SRr_ret; red; exists pos, e, ly, S, (ms_regs msF), (ms_mem msF), mdF;
  split; [rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ msF HS1 eq_refl) at 1; reflexivity|];
  unfold e01_hdr_facts;
  split; [exact HJ0|]; split; [exact Eab|]; split; [exact HGEO|];
  split; [rewrite (e01h_reg_atom (w_H W) _ _ msF regs _ 2%bv 2 HS1 eq_refl ltac:(vm_compute; reflexivity) ltac:(lia)); exact R2|];
  split; [rewrite (e01h_reg_atom (w_H W) _ _ msF regs _ 3%bv 3 HS1 eq_refl ltac:(vm_compute; reflexivity) ltac:(lia)); exact R3|];
  split; [rewrite (e01h_reg_atom (w_H W) _ _ msF regs _ 4%bv 4 HS1 eq_refl ltac:(vm_compute; reflexivity) ltac:(lia)); exact R4|];
  split; [rewrite (e01h_reg_atom (w_H W) _ _ msF regs _ 8%bv 8 HS1 eq_refl ltac:(vm_compute; reflexivity) ltac:(lia)); exact R8|];
  split; [rewrite (e01h_reg_atom (w_H W) _ _ msF regs _ 9%bv 9 HS1 eq_refl ltac:(vm_compute; reflexivity) ltac:(lia)); exact R9|];
  split; [rewrite (e01h_reg_atom (w_H W) _ _ msF regs _ 18%bv 18 HS1 eq_refl ltac:(vm_compute; reflexivity) ltac:(lia)); exact R18|];
  split; [apply (e01h_reg_off (w_H W) _ _ msF 19%bv 32 0 _ HS1 ltac:(vm_compute; reflexivity)); rewrite U32; apply Z.add_0_r|];
  split; [rewrite (e01h_reg_atom (w_H W) _ _ msF regs _ 22%bv 10 HS1 eq_refl ltac:(vm_compute; reflexivity) ltac:(lia)); exact R10|];
  split; [rewrite (e01h_reg_atom (w_H W) _ _ msF regs _ 23%bv 23 HS1 eq_refl ltac:(vm_compute; reflexivity) ltac:(lia)); exact R23|];
  split; [rewrite (e01h_reg_atom (w_H W) _ _ msF regs _ 26%bv 10 HS1 eq_refl ltac:(vm_compute; reflexivity) ltac:(lia)); exact R10|];
  split; [rewrite (e01h_reg_atom (w_H W) _ _ msF regs _ 27%bv 27 HS1 eq_refl ltac:(vm_compute; reflexivity) ltac:(lia)); exact R27|]
end.
split.
(* the frame's 80 shadow bytes, from the chunks of the region at atom 32 *)
- lazymatch type of HS1 with st_ok _ _ ?ssf _ =>
    let i := eval vm_compute in (e01h_find_base (ss_mem ssf) 32) in
    let r := eval vm_compute in (nth_error (ss_mem ssf) i) in
    lazymatch r with Some ?rg =>
    pose proof (HPgSteps.st_ok_region_at _ _ _ i rg HS1 ltac:(vm_compute; reflexivity)) as Hrg end end.
  apply (e01h_fsh_of_region _ _ _ 32 (e_F e) _ _ _ _ _ _ Hrg U32). vm_compute. reflexivity.
(* the carried cells: the 13 saves, the flag word, the three float saves *)
- unfold hq_kept, hq_fsaves in HK |- *.
  destruct HK as [Hc (v0 & v1 & v2 & F0 & F1 & F2)].
  lazymatch type of HS1 with st_ok _ _ _ (restrict _ ?msF) =>
  assert (KV : forall a, spZ (h_regs rsegs hx) - 0x80 <= a -> a + 8 <= spZ (h_regs rsegs hx) ->
    forall v, val_mem rsegs (mrestrict (w_H W) mem) a 8 v -> val_mem rsegs (mrestrict (w_H W) (ms_mem msF)) a 8 v);
  [ intros a Ha1 Ha2 v Hv; apply (val_mem_kept rsegs (w_H W) (w_H W) mem (ms_mem msF)); [|exact Hv];
    intros k Hk; change (Z.of_nat 8) with 8 in Hk;
    destruct (NWs (a + k) ltac:(revert Ha1 Ha2 Hk; clear; intros; lia)) as [Hr Hn];
    exact (KP _ Hr Hn) |] end.
  split.
  + rewrite Forall_forall in Hc |- *. intros f Hf. pose proof (Hc f Hf) as Hf'.
    unfold hq_cells in Hf. apply in_app_or in Hf. destruct Hf as [Hf | [<- | []]].
    * unfold hq_saves_L in Hf. apply in_map_iff in Hf as (j & <- & Hj). apply in_seq in Hj.
      cbn [fst snd hd_at hd_xv] in Hf' |- *.
      apply KV; [revert Hj GS; clear; intros; lia | revert Hj GS; clear; intros; lia | exact Hf'].
    * cbn [fst snd hd_at hd_xv] in Hf' |- *.
      lazymatch goal with |- val_mem _ (mrestrict _ ?mF) _ _ _ =>
      apply (val_mem_kept rsegs (w_H W) (w_H W) mem mF); [|exact Hf'] end.
      intros k Hk. change (Z.of_nat 8) with 8 in Hk. unfold HQ_FLAG.
      destruct (NWfl (e_F e + 0 + 1016 + k) ltac:(revert Hk; clear; intros; lia)) as [Hr Hn].
      exact (KP _ Hr Hn).
  + exists v0, v1, v2. cbn [hd_at hd_xv] in F0, F1, F2 |- *.
    split; [|split].
    * apply KV; [revert GS; clear; intros; lia | revert GS; clear; intros; lia | exact F0].
    * apply KV; [revert GS; clear; intros; lia | revert GS; clear; intros; lia | exact F1].
    * apply KV; [revert GS; clear; intros; lia | revert GS; clear; intros; lia | exact F2].
Qed.
End s.

Print Assumptions e01_hdr_ok.
