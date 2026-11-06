(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: region_kept_tcj_stack and region_kept_tcj_frame are the text of lib/A/ACem.v's
   region_kept_ownframe_aj (copied there from projects/libreac/fuzz_knock/proofs/lib/A/ACem.v) with the call's acall_kept
   replaced by a callee's tcj_kept (lib/A/Prog/CodecCJ.v), cpw_apresent_of_writable that of lib/A/AE7f.v's
   apresent_of_writable; the re-seat in cpw_call_reseat and cpw_rebase is the text of lib/A/AWalkFw2.v's reseatL (copied
   there from projects/libreac/fuzz_knock/proofs/lib/A/AWalkFw2.v) with the environment equation kept for env_agree,
   cpw_kept_std that of lib/A/AWalkFw1.v's aconstsF with the region_kept_val cases of
   projects/reac-pw/fuzz_qdisc/proofs/lib/A/QPgMain3.v:186-194, and cpw_leaf that of lib/A/Prog/CPgWalk.v's cw_leaf with the
   state's layout, astate and model taken through the calls' chain; for libdiginet/fuzz_codec's ASan build (image A).
   cpw_call, cpw_entry, cpw_kept_run, cpw_io, cpw_keep and cpw_sp_off are new. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/A/Prog/CPgWalkCall.v; 852 of its 903 lines of code are new or changed and 227 lines of the source are left out. *)
(* owed_counter_text (fuzz_codec.c:402-429) at image A (fuzz_codec.asan, entry 0x83df8, 302 instructions): the
   walk's own vocabulary, shared by its segment files.
   - Atoms: 0..31 the registers at the entry, 32 the shadow offset SB; 70 = sp1, the stack pointer after the
     prologue's `andi sp,sp,-32`; 75 = F, the class-1 side-stack frame; 87 = the frame's flag address; 88 = SB + F / 8,
     the frame's shadow. The text loop: 300 = the text cursor q + i, 310 + k = s[k], 320 + k = dot[k]; the dead
     registers of a loop head take the atoms 400.. .
   - The frame (framemaps: `f1 x4 | 00 | f2 x3 | 00 x4 | f3 x4`): s[8] at F + 32, dot[8] at F + 64, the header at F,
     the flag word at F + 120; the spills of the prologue at sp1 + 8 .. sp1 + 56 (dt, F, F, F).
   - oc_kstep folds a run's writes into the walk's kept invariant (CPgWalkKept.cw_kept_step): every write is in the
     walk's stack window, in the frame and its shadow (fresh), or in the bytes the contract lets the call write. *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YC85 YCeo.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YI16 YM05 YI00.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YG0s YO0b YO0c.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw0 ACef AF0l ACej ACeh ACem ACep.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw1 AWalkFw2 ACfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require codec_owe codec_text.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase CPgChkC CPgWalk CPgWalkKept CPgWalkFrame CPgWalkCall.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Lemma oc_denot_and_m32 : forall E n v c, ew E n = Z_to_bv 64 v -> 0 <= v + c -> v + c < 2 ^ 64 -> 0 <= v < 2 ^ 64 ->
  sv_denot E (SAlu ALU_AND (SOff n c) (SLit (-32))) = Z_to_bv 64 (32 * ((v + c) / 32)).
Proof.
intros E n v c Hn H0 H1 Hv. rewrite denot_lit_U. f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit, (U_atom_off E n v c Hn) by lia.
change (zcanon (-32)) with (2 ^ 64 - 32). rewrite land_m32 by lia. apply zcanon_id. unfold M64.
split; [apply Z.mul_nonneg_nonneg; [lia | apply Z.div_pos; lia]|].
pose proof (Z.mul_div_le (v + c) 32 ltac:(lia)). lia.
Qed.
Lemma oc_val_mem_zero4 : forall H (m : word -> option byte) a,
  (forall i, 0 <= i < 4 -> aview tfibsegs H m (a + i) = Some 0) -> val_mem tfibsegs (mrestrict H m) a 4 0.
Proof.
intros H m a Hz j Hj. destruct (aview_byte tfibsegs H m (a + Z.of_nat j) 0 (Hz (Z.of_nat j) ltac:(lia))) as (b & Hb & Hv & _).
rewrite Hb. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned. unfold YO0f.le_byte, bv_wrap.
repeat (rewrite Z.shiftr_0_l || rewrite Z.mod_0_l by ((first [lazymatch goal with |- _ <> @nil _ => discriminate end | vm_compute; discriminate]))). lia.
Qed.
Lemma oc_count_le : forall cid l, count_cid cid l <= Z.of_nat (length l).
Proof. intros cid l. induction l as [|[c p] t IH]; cbn [count_cid length]; [lia|]. destruct (c =? cid); lia. Qed.
Lemma oc_region_kept : forall E (H H2 : word -> bool) (m m2 : word -> option byte) n b lo hi wlo whi cs,
  bv_unsigned (ew E n) = b ->
  (forall a, b + lo <= a < b + hi -> aview tfibsegs H2 m2 a = aview tfibsegs H m a) ->
  (forall a, b + wlo <= a < b + whi -> apresent H2 m2 a) ->
  region_kept tfibsegs E (mrestrict H m) (mrestrict H2 m2) (YP09.mkRegion (Some n) lo hi wlo whi cs).
Proof.
intros E H H2 m m2 n b lo hi wlo whi cs Hn Hav Hp.
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hn; intros a Ha.
- apply (mbyte_of_aview tfibsegs). apply Hav. exact Ha.
- intros _. apply (apresent_writable tfibsegs). apply Hp. exact Ha.
Qed.
Lemma oc_kept_of_frame : forall E rs H (m m' : word -> option byte),
  frame_of E rs (mrestrict H m) (mrestrict H m') ->
  forall a, 0 <= a < 2 ^ 64 -> ~ in_wrange E rs a -> aview tfibsegs H m' a = aview tfibsegs H m a.
Proof.
intros E rs H m m' HF a Ha Hn. apply (aview_eq_of tfibsegs). apply HF. rewrite unsigned_lit_small by lia. exact Hn.
Qed.
(* the zone of a state's write windows, region by region: win proves the kept-cover disjunct of one window *)
Ltac oc_cover win :=
  let a := fresh "a" in let r := fresh "r" in let Hr := fresh "Hr" in let Hb := fresh "Hb" in
  intros a (r & Hr & Hb);
  lazymatch type of Hr with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hr end;
  cbn [In] in Hr;
  let rec go :=
    lazymatch type of Hr with
    | False => destruct Hr
    | _ \/ _ => destruct Hr as [<- | Hr];
        [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb;
          first [ win a Hb | match goal with |- ?g => let t := type of Hb in idtac "OC-COVER-FAIL" g t; fail 2 end ]
        | go ]
    end in
  go.
Ltac oc_win a Hb :=
  first
  [ exfalso; clear - Hb; lia
  | lazymatch goal with AGx : forall n, (n < 33)%nat -> _ |- _ => revert Hb; evalE AGx; intros Hb end;
    first
    [ left; unfold T_owed_counter_text, ESTACK;
      lazymatch goal with Hs1 : _ - 176 <= ?s1 <= _ - 160 |- _ => clear - Hb Hs1; lia end
    | lazymatch goal with HFRx : forall x, _ -> cw_fresh _ ?lc ?Sc0 x |- _ => right; right; apply HFRx; clear - Hb; lia end
    | right; right;
      lazymatch goal with
      | HARx : AR _ ?Bv ?l1 ?S1 ?W1 ?m1 ?md1, Hfrsx : frames ?S1 = (1, ?ps) :: frames ?Sc0, LAWSx : AR_laws _ ?Bv,
        FFLx : frame_flag_lawP _ ?Bv |- cw_fresh _ ?lc ?Sc0 _ =>
        apply (cw_fresh_frame Bv LAWSx FFLx l1 S1 W1 m1 md1 lc Sc0 1 ps a HARx Hfrsx);
        [ first [ lazymatch goal with Eabx : ablocks ?Bv l1 S1 = ablocks ?Bv lc Sc0 |- _ =>
                    intros ? ?; rewrite Eabx; tauto end
                | lazymatch goal with HPx : Permutation (ablocks ?Bv l1 S1) (ablocks ?Bv lc Sc0) |- _ =>
                    intros ? ?; split; [apply (Permutation_in _ HPx) | apply (Permutation_in _ (Permutation_sym HPx))] end ]
        | first [ intros ? ?; reflexivity | assumption ]
        | unfold frame_rng, in_zr, shadow_addr, SHADOW_OFF; cbn [fst snd];
          change (fs_frame_bytes 1) with 128; change (128 / 8) with 16;
          try (lazymatch goal with EFx : forall c p, frame_addr l1 c p = frame_addr lc c p |- _ => rewrite ?EFx end);
          try (lazymatch goal with EFLx : forall c p, flag_addr l1 c p = flag_addr lc c p |- _ => rewrite ?EFLx end);
          try (lazymatch goal with HFx : ?Fv = frame_addr ?lz 1 ps |- _ => rewrite <- HFx end);
          try (lazymatch goal with HFLx : ?FLv = flag_addr ?lz 1 ps |- _ => rewrite <- HFLx end);
          first [left; lia | right; left; lia | right; right; lia] ]
      end ] ].
(* fold the run's frame into the kept invariant HK (CPgWalkKept.cw_kept_step) *)
Ltac oc_kstep win :=
  first [
  lazymatch goal with
  | HFr : frame_of ?Ef ?rs (mrestrict ?H ?m1) (mrestrict _ ?m2), HG : mem_grows _ _,
    HK : tcj_kept _ ?Bv ?T ?lyc ?Sc ?W ?m0 ?W1 _ ?sp ?Eo, LAWSx : AR_laws _ ?Bv,
    HARx : AR _ ?Bv ?lyc ?Sc ?W ?m0 ?mdx |- _ =>
    let HK' := fresh "HK" in
    pose proof (cw_kept_step Bv LAWSx T lyc Sc W m0 mdx W1 m1 m2 sp Eo (in_wrange Ef rs) ltac:(lia) HARx HK
      (oc_kept_of_frame Ef rs H m1 m2 HFr)) as HK';
    specialize (HK' ltac:(oc_cover win));
    specialize (HK' (fun a Hp => apresent_grows H m1 m2 a HG Hp));
    clear HK HFr HG; rename HK' into HK
  end
  | match goal with HFr : frame_of _ _ _ _ |- _ => let t := type of HFr in idtac "KSTEP-HFR" t end;
    match goal with HK : tcj_kept _ _ _ _ _ _ _ _ _ _ _ |- _ => let t := type of HK in idtac "KSTEP-HK" t end;
    fail ]; clear_frames; repeat (rewrite wvb_collapse in * ).
(* the write windows of the walk's regions: read-only, the save area of atom 2, the spill slots of atom 70 *)
Ltac oc_stk_lia :=
  unfold T_owed_counter_text, ESTACK in *;
  lazymatch goal with
  | Hl : ?s0 - ?stk <= spZ ?r - _, Hh : spZ ?r <= ?s0, Hs1 : _ - 176 <= ?x1 <= _ - 160 |- _ => clear - Hl Hh Hs1; lia
  | Hl : ?s0 - ?stk <= spZ ?r - _, Hh : spZ ?r <= ?s0 |- _ => clear - Hl Hh; lia
  end.
Ltac oc_awr :=
  lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
  let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0 bc ly own) end;
  lazymatch goal with AGx : forall n, (n < 33)%nat -> _ |- _ =>
  repeat lazymatch goal with
  | |- awr_ok _ [] _ _ _ _ _ _ _ => apply awr_ok_nil
  | |- awr_ok _ (YP09.mkRegion _ _ _ ?wlo ?whi _ :: _) _ _ _ _ _ _ _ =>
     first
     [ lazymatch (eval vm_compute in (Z.leb whi wlo)) with true => apply awr_ok_cons_ro; [clear; cbn; lia|] end
     | lazymatch goal with Ux : bv_unsigned (ew _ 2) = ?spv, Hsp0 : ?spv <= ?s0 |- awr_ok _ _ _ ?s0 _ _ _ _ _ =>
       eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (spv - s0));
       [reflexivity | evalE AGx; clear; lia | cbn [YP09.r_wlo YP09.r_whi]; oc_stk_lia | cbn [YP09.r_wlo YP09.r_whi]; oc_stk_lia |] end
     | lazymatch goal with E70x : ew _ 70 = Z_to_bv 64 ?s1, Hsp0 : _ <= ?s0 |- awr_ok _ _ _ ?s0 _ _ _ _ _ =>
       eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 70%nat (s1 - s0));
       [reflexivity | evalE AGx; clear; lia | cbn [YP09.r_wlo YP09.r_whi]; oc_stk_lia | cbn [YP09.r_wlo YP09.r_whi]; oc_stk_lia |] end
     | lazymatch goal with HFx : ?Fv = frame_addr _ 1 ?ps |- _ =>
       eapply (cw_awr_ok_cons_frame _ _ _ _ _ _ _ _ _ _ 1 ps 75%nat);
       [reflexivity | evalE AGx; try (lazymatch goal with EFx : forall c p, frame_addr ?l1 c p = frame_addr ?l2 c p |- _ => rewrite EFx end); exact HFx
       | left; reflexivity | clear; cbn; lia | clear; cbn; change (fs_frame_bytes 1) with 128; lia |] end
     | lazymatch goal with HFx : ?Fv = frame_addr _ 1 ?ps |- _ =>
       eapply (cw_awr_ok_cons_fshadow _ _ _ _ _ _ _ _ _ _ 1 ps 88%nat);
       [reflexivity | evalE AGx; try (lazymatch goal with EFx : forall c p, frame_addr ?l1 c p = frame_addr ?l2 c p |- _ => rewrite EFx end);
          unfold shadow_addr, SHADOW_OFF; rewrite <- HFx; reflexivity | left; reflexivity | clear; cbn; lia
       | clear; cbn; change (fs_frame_bytes 1 / 8) with 16; lia |] end ]
  end end.
(* the engine's shadow table: empty (the frame's checks read the frame's shadow region) *)
Ltac oc_reshok HS :=
  try match goal with H : sh_ok _ _ _ _ _ |- _ => clear H end;
  lazymatch type of HS with st_ok _ ?Ex _ (restrict (w_H ?Wx) ?msx) =>
  let SH := fresh "SHOK" in assert (SH : sh_ok tfibsegs CW_Bx [] Ex (mrestrict (w_H Wx) (ms_mem msx))) by constructor end.


(* ================================ state plumbing ================================ *)
Section sp. Context {fx : YK11.FPState}.
(* the first region's first chunk read through another symbolic value with the same denotation *)
Lemma oc_swap0 : forall E ss ms b lo hi wlo whi o w v v' cs rs,
  st_ok tfibsegs E ss ms ->
  ss_mem ss = YP09.mkRegion b lo hi wlo whi (YP09.mkChunk o (CVal w v) :: cs) :: rs ->
  sv_denot E v' = sv_denot E v ->
  st_ok tfibsegs E (mkSS (ss_pc ss) (ss_regs ss) (YP09.mkRegion b lo hi wlo whi (YP09.mkChunk o (CVal w v') :: cs) :: rs)
    (ss_resv ss) (ss_facts ss)) ms.
Proof.
intros E ss ms b lo hi wlo whi o w v v' cs rs (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9) Hm Hv.
unfold st_ok; cbn. repeat (split; [assumption|]). split; [|exact H9].
rewrite Hm in H8. destruct H8 as (Hwf & Hok & Hpd).
split; [cbn [regions_wf region_wf forallb chunk_inside YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks YP09.c_off
  c_len cv_len YP09.c_val] in *; exact Hwf|].
split; [|revert Hpd; cbn [pairwise_disjoint]; intros [Ha Hp]; split; [|exact Hp]; clear - Ha;
  induction rs as [|r1 rs IH]; cbn [all_disjoint] in *; [exact I | destruct Ha as [Ha1 Ha2]; split; [exact Ha1 | exact (IH Ha2)]]].
inversion Hok as [|r0 rs0 Hr0 Hrs]; subst. constructor; [|exact Hrs].
destruct Hr0 as (R1 & R2 & R3 & R4). split; [exact R1|]. split; [exact R2|]. split; [exact R3|].
inversion R4 as [|c0 cs0 Hc0 Hcs]; subst. constructor; [|exact Hcs].
intros i Hi. destruct (Hc0 i Hi) as (bt & Hb & Hm2). exists bt. split; [|exact Hm2].
cbn [YP09.c_off YP09.c_val cbyte] in *. rewrite Hv. exact Hb.
Qed.
(* replace the registers by others with the same denotations; the machine is unchanged *)
Lemma oc_regs_lit : forall E ss ms (r : bv 5),
  st_ok tfibsegs E ss ms -> r <> 0%bv ->
  st_ok tfibsegs E (mkSS (ss_pc ss) (sr_set (ss_regs ss) r (SLit (bv_unsigned (getr (ms_regs ms) r)))) (ss_mem ss) (ss_resv ss)
    (ss_facts ss)) ms.
Proof.
intros E ss ms r HS Hr. apply (st_ok_pin_rege E ss ms r _ HS Hr). cbn [sv_denot]. apply Z_to_bv_bv_unsigned.
Qed.
End sp.
(* AG (the base registers and SB as the entry's) from HAE : env_agree 32 E0 E and E32 *)
Ltac oc_AG E0 :=
  try match goal with AGx : forall n, (n < 33)%nat -> _ |- _ => clear AGx end;
  lazymatch goal with HAE : env_agree 32 E0 ?Ev, E32x : ew ?Ev 32 = Z_to_bv 64 SB, E32o : ew E0 32 = Z_to_bv 64 SB |- _ =>
  let AG := fresh "AG" in
  assert (AG : forall n, (n < 33)%nat -> ew Ev n = ew E0 n)
    by (let nn := fresh "nn" in let Hn := fresh "Hn" in intros nn Hn;
        destruct (Nat.eq_dec nn 32) as [-> | Hne]; [rewrite E32x, E32o; reflexivity | apply (proj1 HAE); lia])
  end.

(* ================================ the loop head 0x83f48 ================================ *)
Definition OC_A : Z := 0x83df8.
Definition OC_SEG7 : Z := 0x8438c.
(* the frame's shadow map after the prologue (0x83ee4 .. 0x83f28): f1 x4, 00, f2 x3, 00 x4, f3 x4, as the
   engine's 64-bit literals of the sign-extended bytes *)
Definition oc_fs_chunks : list YP09.chunk :=
  [YP09.mkChunk 0 (CVal 1 (SLit 18446744073709551601)); YP09.mkChunk 1 (CVal 1 (SLit 18446744073709551601));
   YP09.mkChunk 2 (CVal 1 (SLit 18446744073709551601)); YP09.mkChunk 3 (CVal 1 (SLit 18446744073709551601));
   YP09.mkChunk 4 (CVal 1 (SLit 0));
   YP09.mkChunk 5 (CVal 1 (SLit 18446744073709551602)); YP09.mkChunk 6 (CVal 1 (SLit 18446744073709551602));
   YP09.mkChunk 7 (CVal 1 (SLit 18446744073709551602));
   YP09.mkChunk 8 (CVal 1 (SLit 0)); YP09.mkChunk 9 (CVal 1 (SLit 0));
   YP09.mkChunk 10 (CVal 1 (SLit 0)); YP09.mkChunk 11 (CVal 1 (SLit 0));
   YP09.mkChunk 12 (CVal 1 (SLit 18446744073709551603)); YP09.mkChunk 13 (CVal 1 (SLit 18446744073709551603));
   YP09.mkChunk 14 (CVal 1 (SLit 18446744073709551603)); YP09.mkChunk 15 (CVal 1 (SLit 18446744073709551603))].
Definition oc_fs_ro : YP09.region := YP09.mkRegion (Some 88%nat) 0 16 0 0 oc_fs_chunks.
(* dot[] after n digits: the set flags dot[n - 1] .. dot[0] (atoms 320 + k, newest first, as the engine's stores
   leave them), then the clear ones dot[n] .. dot[7] *)
Definition oc_dot_chunks (n : nat) : list YP09.chunk :=
  map (fun k => YP09.mkChunk (64 + 4 * Z.of_nat k) (CVal 4 (SOff (320 + k) 0))) (rev (seq 0 n)) ++
  map (fun k => YP09.mkChunk (64 + 4 * Z.of_nat k) (CVal 4 (SLit 0))) (seq n (8 - n)).
Definition oc_dot (n : nat) : YP09.region := YP09.mkRegion (Some 75%nat) 64 96 64 96 (oc_dot_chunks n).
(* s[] after n digits: s[n - 1] .. s[0] (atoms 310 + k, newest first) *)
Definition oc_s (n : nat) : YP09.region :=
  YP09.mkRegion (Some 75%nat) 32 40 32 40 (map (fun k => YP09.mkChunk (32 + Z.of_nat k) (CVal 1 (SOff (310 + k) 0))) (rev (seq 0 n))).
Definition oc_fl : YP09.region := YP09.mkRegion (Some 75%nat) 120 128 120 120 [YP09.mkChunk 120 (CVal 8 (SOff 87 0))].
Definition oc_r70 : YP09.region := YP09.mkRegion (Some 70%nat) 8 56 8 56
  [YP09.mkChunk 16 (CVal 8 (SOff 75 0)); YP09.mkChunk 48 (CVal 8 (SOff 75 0));
   YP09.mkChunk 24 (CVal 8 (SOff 75 0)); YP09.mkChunk 8 (CVal 8 (SOff 12 0))].
Definition oc_saves : list YP09.chunk :=
  [YP09.mkChunk (-104) (CVal 8 (SOff 27 0)); YP09.mkChunk (-96) (CVal 8 (SOff 26 0));
   YP09.mkChunk (-88) (CVal 8 (SOff 25 0)); YP09.mkChunk (-80) (CVal 8 (SOff 24 0));
   YP09.mkChunk (-72) (CVal 8 (SOff 23 0)); YP09.mkChunk (-64) (CVal 8 (SOff 22 0));
   YP09.mkChunk (-56) (CVal 8 (SOff 21 0)); YP09.mkChunk (-48) (CVal 8 (SOff 20 0));
   YP09.mkChunk (-40) (CVal 8 (SOff 19 0)); YP09.mkChunk (-32) (CVal 8 (SOff 18 0));
   YP09.mkChunk (-24) (CVal 8 (SOff 9 0)); YP09.mkChunk (-16) (CVal 8 (SOff 8 0));
   YP09.mkChunk (-8) (CVal 8 (SOff 1 0))].
Definition oc_stack : YP09.region := YP09.mkRegion (Some 2%nat) (-104) 0 (-104) 0 oc_saves.
Definition oc_atoms : list (nat * afact) :=
  [(88%nat, mkAF 2147451392 17594333495296 2); (87%nat, HPTR 0); (75%nat, HPTR 5);
   (70%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF SB SB 0)].
Definition oc_alias : list (sv * sv) := [(SAlu ALU_ADD (SAlu ALU_SRL (SOff 75 0) (SLit 3)) (SOff 32 0), SOff 88 0)].
Definition oc_facts : facts := mkFacts oc_atoms [] oc_alias.
(* the registers kept live at the loop head: sp = s1 = sp1, s0 = the entry sp, gp, tp, s2 = n, s3 = '.', s4 = seg,
   s5 = dot, s6 = s7 = the cursor, s8 = the frame's shadow, s10 = SB, s11 = s *)
Definition ocL_regs (n : nat) : list sv :=
  [SLit 0; SOff 1 0; SOff 70 0; SOff 3 0; SOff 4 0; SOff 5 0; SOff 6 0; SOff 7 0;
   SOff 2 0; SOff 70 0; SOff 10 0; SOff 11 0; SOff 12 0; SOff 13 0; SOff 14 0; SOff 15 0;
   SOff 16 0; SOff 17 0; SLit (Z.of_nat n); SLit 46; SOff 11 0; SOff 75 64; SOff 300 0; SOff 300 0;
   SOff 88 0; SOff 25 0; SOff 32 0; SOff 75 32; SOff 28 0; SOff 29 0; SOff 30 0; SOff 31 0].
Definition oc_deads : list nat := [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 25; 28; 29; 30; 31]%nat.
Definition oc_deads_bv : list (bv 5) := [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 25; 28; 29; 30; 31]%bv.
Definition OC_RT : nat := 400.
Definition ss_L (n : nat) : sstate :=
  ss_havoc_regs (mkSS 0x83f48 (ocL_regs n) [oc_dot n; oc_fs_ro; oc_s n; oc_fl; oc_r70; oc_stack] None oc_facts) OC_RT oc_deads.

(* the join to a loop-head state tg: the dead registers into the window OC_RT, the regions and the facts of tg *)
Ltac oc_join HS tg :=
  norm_ss HS;
  lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
    let dl := eval cbv in oc_deads_bv in
    let vals := constr:(map (fun r : bv 5 => getr (ms_regs msx) r) dl) in
    let vals' := eval cbn [map ms_regs restrict] in vals in
    let HS3 := fresh "HS3" in
    pose proof (st_ok_havoc_win tfibsegs OC_RT Ex ssx msx vals' HS ltac:(vm_compute; reflexivity)) as HS3;
    clear HS; rename HS3 into HS;
    set_regs_rec HS OC_RT vals' 0%nat dl end;
  norm_ss HS;
  lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
    let rs := eval vm_compute in (ss_mem tg) in
    let HS3 := fresh "HS3" in
    pose proof (st_ok_submem tfibsegs Ex ssx msx rs HS ltac:(cbn [ss_mem]; submem_to) ltac:(vm_compute; reflexivity)) as HS3;
    clear HS; rename HS3 into HS end;
  norm_ss HS;
  lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
    let HS3 := fresh "HS3" in
    pose proof (st_ok_facts_incl3 tfibsegs Ex ssx msx oc_atoms [] oc_alias HS ltac:(incl_lit_tac) ltac:(incl_lit_tac)
      ltac:(incl_lit_tac)) as HS3;
    clear HS; rename HS3 into HS end;
  norm_ss HS;
  lazymatch type of HS with st_ok _ _ ?ssx _ =>
    first [change ssx with tg in HS | let t := eval vm_compute in tg in idtac "OC-JOIN-MISMATCH" ssx t; fail 1] end.

Lemma oc_ew_havoc1 : forall E k w, ew (havoc E k [w]) k = w.
Proof. intros E k w. unfold havoc. cbn [ew]. rewrite Nat.ltb_irrefl, Nat.sub_diag. reflexivity. Qed.

Fixpoint oc_regs_using (sr : list sv) (ks : list nat) (i : nat) : list (bv 5) :=
  match sr with
  | [] => []
  | e :: t => if sv_atoms_on (fun n => negb (existsb (Nat.eqb n) ks)) e then oc_regs_using t ks (S i)
              else Z_to_bv 5 (Z.of_nat i) :: oc_regs_using t ks (S i)
  end.

(* the join to a boundary state tg (dead registers dl in the window OC_RT): keep tg's facts and regions, put each
   dead register's machine value in a literal (freeing the window), then into the window's atom *)
Ltac oc_lit_regs HS rl :=
  lazymatch rl with
  | [] => idtac
  | ?r :: ?rl' =>
    lazymatch type of HS with st_ok _ ?Ev ?ssx ?msx =>
      let HS3 := fresh "HS3" in
      pose proof (oc_regs_lit Ev ssx msx r HS ltac:(discriminate)) as HS3; clear HS; rename HS3 into HS; norm_ss HS end;
    oc_lit_regs HS rl'
  end.
Ltac oc_joinX HS tg dl :=
  norm_ss HS;
  lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
    let fa := eval vm_compute in (f_atoms (ss_facts tg)) in
    let al := eval vm_compute in (f_alias (ss_facts tg)) in
    let HS3 := fresh "HS3" in
    pose proof (st_ok_facts_incl3 tfibsegs Ex ssx msx fa [] al HS ltac:(incl_lit_tac) ltac:(incl_lit_tac)
      ltac:(incl_lit_tac)) as HS3;
    clear HS; rename HS3 into HS end;
  norm_ss HS;
  lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
    let rs := eval vm_compute in (ss_mem tg) in
    let HS3 := fresh "HS3" in
    pose proof (st_ok_submem tfibsegs Ex ssx msx rs HS ltac:(cbn [ss_mem]; submem_to) ltac:(vm_compute; reflexivity)) as HS3;
    clear HS; rename HS3 into HS end;
  norm_ss HS;
  let dlb := eval cbv in (map (fun n => Z_to_bv 5 (Z.of_nat n)) dl) in
  oc_lit_regs HS dlb;
  lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
    let vals := constr:(map (fun r : bv 5 => getr (ms_regs msx) r) dlb) in
    let vals' := eval cbn [map ms_regs restrict] in vals in
    let HS3 := fresh "HS3" in
    pose proof (st_ok_havoc_win tfibsegs 400 Ex ssx msx vals' HS ltac:(vm_compute; reflexivity)) as HS3;
    clear HS; rename HS3 into HS;
    set_regs_rec HS 400%nat vals' 0%nat dlb end;
  norm_ss HS;
  lazymatch type of HS with st_ok _ _ ?ssx _ =>
    first [change ssx with tg in HS | let t := eval vm_compute in tg in idtac "OC-JOIN-MISMATCH" ssx t; fail 1] end.

(* the index of the frame's shadow region (base atom 88) in a state *)
Fixpoint oc_find88 (rs : smem) : nat :=
  match rs with [] => 0%nat | r :: t => match YP09.r_base r with Some 88%nat => 0%nat | _ => S (oc_find88 t) end end.

(* the join to a loop head ss_L n: as oc_joinX, and the cursor registers s6 = s7 (SOff 300 1 after the step) into a
   fresh atom 300 holding their value (Rcur names it) *)
Ltac oc_joinL0 HS tg :=
  norm_ss HS;
  lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict ?Hh ?msx) =>
    let Rc := fresh "Rc" in
    assert (Rc : getr (ms_regs msx) (23%bv : bv 5) = getr (ms_regs msx) (22%bv : bv 5))
      by (rewrite (st_ok_restrict_reg tfibsegs Hh Ex ssx msx (23%bv : bv 5) HS),
                  (st_ok_restrict_reg tfibsegs Hh Ex ssx msx (22%bv : bv 5) HS); reflexivity);
    let Rcur := fresh "Rcur" in
    assert (Rcur : getr (ms_regs msx) (22%bv : bv 5) = sv_denot Ex (SOff 300 1))
      by (rewrite (st_ok_restrict_reg tfibsegs Hh Ex ssx msx (22%bv : bv 5) HS); reflexivity)
  end;
  lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
    let fa := eval vm_compute in (f_atoms (ss_facts tg)) in
    let al := eval vm_compute in (f_alias (ss_facts tg)) in
    let HS3 := fresh "HS3" in
    pose proof (st_ok_facts_incl3 tfibsegs Ex ssx msx fa [] al HS ltac:(incl_lit_tac) ltac:(incl_lit_tac)
      ltac:(incl_lit_tac)) as HS3;
    clear HS; rename HS3 into HS end;
  norm_ss HS;
  lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
    let rs := eval vm_compute in (ss_mem tg) in
    let HS3 := fresh "HS3" in
    pose proof (st_ok_submem tfibsegs Ex ssx msx rs HS ltac:(cbn [ss_mem]; submem_to) ltac:(vm_compute; reflexivity)) as HS3;
    clear HS; rename HS3 into HS end;
  norm_ss HS;
  let dlb := eval cbv in (map (fun n => Z_to_bv 5 (Z.of_nat n)) oc_deads) in
  let dl2 := eval cbv in (dlb ++ [(22%bv : bv 5); (23%bv : bv 5)]) in
  oc_lit_regs HS dl2;
  lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
    let vals := constr:(map (fun r : bv 5 => getr (ms_regs msx) r) dlb) in
    let vals' := eval cbn [map ms_regs restrict] in vals in
    let HS3 := fresh "HS3" in
    pose proof (st_ok_havoc_win tfibsegs 400 Ex ssx msx vals' HS ltac:(vm_compute; reflexivity)) as HS3;
    clear HS; rename HS3 into HS;
    set_regs_rec HS 400%nat vals' 0%nat dlb end;
  norm_ss HS;
  lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
    let w := constr:(getr (ms_regs msx) (22%bv : bv 5)) in
    let w' := eval cbn [ms_regs restrict] in w in
    let HS3 := fresh "HS3" in
    pose proof (st_ok_havoc_win tfibsegs 300 Ex ssx msx [w'] HS ltac:(vm_compute; reflexivity)) as HS3;
    clear HS; rename HS3 into HS;
    set_regs_rec HS 300%nat [w'] 0%nat [(22%bv : bv 5)] end;
  norm_ss HS;
  lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
    let HS3 := fresh "HS3" in
    pose proof (ast_ok_set_reg_fp tfibsegs Ex ssx msx (23%bv : bv 5) (SOff 300 0) HS ltac:(vm_compute; reflexivity)
      ltac:(rewrite sv_denot_SOff0, (ew_havoc_new _ 300 _ 0 (Z_to_bv 64 0)) by (cbn [length]; lia); cbn [nth ms_regs restrict];
            first [symmetry; assumption | assumption])) as HS3;
    clear HS; rename HS3 into HS end;
  norm_ss HS.
Ltac oc_joinL HS tg :=
  oc_joinL0 HS tg;
  lazymatch type of HS with st_ok _ _ ?ssx _ =>
    first [change ssx with tg in HS | let t := eval vm_compute in tg in idtac "OC-JOIN-MISMATCH" ssx t; fail 1] end.
(* the merge path: the dot flag dot[n - 1] stored as the literal 1 (the head chunk of the dot region once the text
   byte's region is dropped) into the fresh atom k = 320 + n - 1 (its old value is no longer used) *)
Ltac oc_joinM HS tg k :=
  norm_ss HS;
  lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
    let rs := eval vm_compute in (tl (ss_mem ssx)) in
    let HS3 := fresh "HS3" in
    pose proof (st_ok_submem tfibsegs Ex ssx msx rs HS ltac:(cbn [ss_mem]; submem_to) ltac:(vm_compute; reflexivity)) as HS3;
    clear HS; rename HS3 into HS end;
  norm_ss HS;
  lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
    let fa := eval vm_compute in (f_atoms (ss_facts tg)) in
    let al := eval vm_compute in (f_alias (ss_facts tg)) in
    let HS3 := fresh "HS3" in
    pose proof (st_ok_facts_incl3 tfibsegs Ex ssx msx fa [] al HS ltac:(incl_lit_tac) ltac:(incl_lit_tac)
      ltac:(incl_lit_tac)) as HS3;
    clear HS; rename HS3 into HS end;
  norm_ss HS;
  lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
    let rl := eval vm_compute in (oc_regs_using (ss_regs ssx) [k] 0) in oc_lit_regs HS rl end;
  norm_ss HS;
  lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
    let HS3 := fresh "HS3" in
    first [ pose proof (st_ok_havoc_win tfibsegs k Ex ssx msx [Z_to_bv 64 1] HS ltac:(vm_compute; reflexivity)) as HS3
          | let m := eval vm_compute in (ss_mem ssx) in let r := eval vm_compute in (ss_regs ssx) in idtac "JM-HAVOC" m r; fail 1 ];
    clear HS; rename HS3 into HS end;
  norm_ss HS;
  lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
    lazymatch eval vm_compute in (ss_mem ssx) with YP09.mkRegion ?b ?lo ?hi ?wlo ?whi (YP09.mkChunk ?o (CVal ?w ?v) :: ?cs) :: ?rs =>
      let HS3 := fresh "HS3" in
      pose proof (oc_swap0 Ex ssx msx b lo hi wlo whi o w v (SOff k 0) cs rs HS ltac:(vm_compute; reflexivity)
        ltac:(rewrite sv_denot_SOff0, oc_ew_havoc1; reflexivity)) as HS3;
      clear HS; rename HS3 into HS end end;
  norm_ss HS;
  oc_joinL0 HS tg;
  lazymatch type of HS with st_ok _ _ ?ssx _ =>
    first [change ssx with tg in HS | let t := eval vm_compute in tg in idtac "OC-JOIN-MISMATCH" ssx t; fail 1] end.

(* the text-end stop 0x8405c (beqz s9 taken): the loop head's registers, the cursor dead *)
Definition ocZ_deads : list nat := [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 22; 23; 25; 28; 29; 30; 31]%nat.
Definition ss_Z (n : nat) : sstate :=
  ss_havoc_regs (mkSS 0x8405c (ocL_regs n) [oc_dot n; oc_fs_ro; oc_s n; oc_fl; oc_r70; oc_stack] None oc_facts) OC_RT ocZ_deads.
(* the release 0x84174: a0 = the return code (the literal z), s0 = the entry sp, s1 = sp1, s8 = the frame's shadow;
   every other register is reloaded by the epilogue or dead *)
Definition ocR_regs (z : Z) : list sv :=
  [SLit 0; SOff 1 0; SOff 70 0; SOff 3 0; SOff 4 0; SOff 5 0; SOff 6 0; SOff 7 0;
   SOff 2 0; SOff 70 0; SLit z; SOff 11 0; SOff 12 0; SOff 13 0; SOff 14 0; SOff 15 0;
   SOff 16 0; SOff 17 0; SOff 18 0; SOff 19 0; SOff 20 0; SOff 21 0; SOff 22 0; SOff 23 0;
   SOff 88 0; SOff 25 0; SOff 26 0; SOff 27 0; SOff 28 0; SOff 29 0; SOff 30 0; SOff 31 0].
Definition ocR_deads : list nat :=
  [1; 5; 6; 7; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 25; 26; 27; 28; 29; 30; 31]%nat.
Definition ss_R (z : Z) : sstate :=
  ss_havoc_regs (mkSS 0x84174 (ocR_regs z) [oc_fs_ro; oc_fl; oc_r70; oc_stack] None oc_facts) OC_RT ocR_deads.

(* ================================ the call and its boundaries ================================ *)
Record occx := mkOC {
  o_STK : Z; o_sp0 : Z; o_FP : list (Z * Z); o_ly : alayout; o_S : astate; o_W0 : world tfibsegs;
  o_mem0 : word -> option byte; o_md0 : Model; o_own : list (Z * Z);
  o_lyc : alayout; o_Sc : astate; o_W : world tfibsegs; o_memc : word -> option byte; o_mdc : Model; o_k : Z;
  o_regs : bvmap 5 word; o_q : Z; o_sg : Z; o_dt : Z; o_tb : list Z; o_sj : list Z; o_dj : Z;
  o_pos : Z }.
Definition oc_E (cx : occx) : Z -> Prop := fun x => o_sg cx <= x < o_sg cx + 8 \/ o_dt cx <= x < o_dt cx + 1.
Definition oc_sp1 (cx : occx) : Z := 32 * ((spZ (o_regs cx) + -160) / 32).
Definition oc_F (cx : occx) : Z := frame_addr (o_lyc cx) 1 (o_pos cx).
Definition oc_FL (cx : occx) : Z := flag_addr (o_lyc cx) 1 (o_pos cx).
Definition oc_n (cx : occx) : Z := Z.of_nat (length (o_tb cx)).
Section ctx. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Variable GLYPHA : Z.
Variable ROSTRS : list (Z * Z).
Local Notation rd W mem := (mrestrict (w_H W) mem).
(* the contract's premises (CPgChkC.cdc_owed_counter_text_specX at RLO / RHI = CA_RLO / CA_RHI) *)
Definition oc_pre (cx : occx) : Prop :=
  cdc_entry tfibsegs B (o_STK cx) (o_sp0 cx) (o_FP cx) (o_ly cx) (o_S cx) (o_W0 cx) (o_mem0 cx) (o_md0 cx) (o_own cx)
    (o_lyc cx) (o_Sc cx) (o_W cx) (o_memc cx) (o_mdc cx) (o_k cx) (o_regs cx) T_owed_counter_text /\
  getr (o_regs cx) 10 = w64 (o_q cx) /\
  cstr_rd tfibsegs (o_W cx) (o_memc cx) (spZ (o_regs cx)) T_owed_counter_text (o_q cx) (o_tb cx) /\
  cobj_ok B (o_lyc cx) (o_Sc cx) (o_q cx) (oc_n cx) /\ cobj_ok B (o_lyc cx) (o_Sc cx) (o_sg cx) 8 /\
  getr (o_regs cx) 11 = w64 (o_sg cx) /\
  cdst_ok tfibsegs B (o_STK cx) (o_sp0 cx) (o_FP cx) (o_ly cx) (o_S cx) (o_lyc cx) (o_Sc cx) (o_own cx) (o_W cx)
    (o_memc cx) (spZ (o_regs cx)) T_owed_counter_text (o_sg cx) 8 /\
  garr8 tfibsegs (rd (o_W cx) (o_memc cx)) (o_sg cx) (o_sj cx) /\ length (o_sj cx) = 8%nat /\
  getr (o_regs cx) 12 = w64 (o_dt cx) /\
  ((cdst_ok tfibsegs B (o_STK cx) (o_sp0 cx) (o_FP cx) (o_ly cx) (o_S cx) (o_lyc cx) (o_Sc cx) (o_own cx) (o_W cx)
      (o_memc cx) (spZ (o_regs cx)) T_owed_counter_text (o_dt cx) 1 /\ cobj_ok B (o_lyc cx) (o_Sc cx) (o_dt cx) 1) \/
   cdstk_ok tfibsegs B (o_STK cx) (o_sp0 cx) (o_FP cx) (o_ly cx) (o_S cx) (o_lyc cx) (o_Sc cx) (o_own cx) (o_W cx)
      (o_memc cx) (spZ (o_regs cx)) T_owed_counter_text (o_dt cx) 1) /\
  val_mem tfibsegs (rd (o_W cx) (o_memc cx)) (o_dt cx) 1 (o_dj cx) /\
  (o_sg cx + 8 <= o_dt cx \/ o_dt cx + 1 <= o_sg cx) /\
  (o_q cx + oc_n cx <= o_sg cx \/ o_sg cx + 8 <= o_q cx) /\
  (o_q cx + oc_n cx <= o_dt cx \/ o_dt cx + 1 <= o_q cx) /\
  cimg_rd tfibsegs B CA_RLO CA_RHI (o_W cx) (o_memc cx) (spZ (o_regs cx)) T_owed_counter_text ((GLYPHA, 464) :: ROSTRS) /\
  Z.of_nat (length (frames (o_Sc cx))) <= 8.
(* the contract's post *)
Definition oc_R (cx : occx) : world tfibsegs -> (word -> option byte) -> bvmap 5 word -> Prop :=
  fun W2 mem2 regs2 =>
     let '(r, s, d) := codec_owe.owed_counter_text_spec (o_tb cx) in
     getr regs2 10 = w64 r /\
     (r = 0 -> garr8 tfibsegs (rd W2 mem2) (o_sg cx) s /\ val_mem tfibsegs (rd W2 mem2) (o_dt cx) 1 d) /\
     (r <> 0 -> exists s' d', garr8 tfibsegs (rd W2 mem2) (o_sg cx) s' /\ length s' = 8%nat /\
                              val_mem tfibsegs (rd W2 mem2) (o_dt cx) 1 d').
Definition oc_post (cx : occx) : world tfibsegs -> config -> Prop :=
  cdc_post tfibsegs B MT (o_STK cx) (o_sp0 cx) (o_FP cx) (o_ly cx) (o_S cx) (o_W0 cx) (o_mem0 cx) (o_md0 cx) (o_own cx)
    (o_k cx) (o_regs cx) T_owed_counter_text (oc_E cx) (o_lyc cx) (o_Sc cx) (o_W cx) (o_memc cx) (o_mdc cx) (oc_R cx).
(* the walk's fixed atoms *)
Definition oc_env (cx : occx) (E : env) : Prop :=
  env_agree 32 (Ereg (o_regs cx) (cw_extra [])) E /\ ew E 32 = Z_to_bv 64 SB /\
  ew E 70 = Z_to_bv 64 (oc_sp1 cx) /\ ew E 75 = Z_to_bv 64 (oc_F cx) /\ ew E 87 = Z_to_bv 64 (oc_FL cx) /\
  ew E 88 = Z_to_bv 64 (SB + oc_F cx / 8).
(* what every boundary after the frame request carries: the caller's journal with the frame in front of own,
   the frames, blocks, meter and model of the call state, and the kept invariant *)
Definition oc_st (cx : occx) (ly3 : alayout) (S3 : astate) (W3 : world tfibsegs) (m3 : word -> option byte) (md3 : Model) : Prop :=
  ajournal tfibsegs B (o_STK cx) (o_sp0 cx) (o_FP cx) (o_ly cx) (o_S cx) (o_W0 cx) (o_mem0 cx) (o_md0 cx)
    ((1, o_pos cx) :: o_own cx) ly3 S3 W3 m3 md3 (o_k cx) /\
  frames S3 = (1, o_pos cx) :: frames (o_Sc cx) /\ ~ In (1, o_pos cx) (frames (o_Sc cx)) /\
  Permutation (ablocks B ly3 S3) (ablocks B (o_lyc cx) (o_Sc cx)) /\ mo_le MT (o_Sc cx) S3 0 /\ same_io (o_mdc cx) md3 /\
  tcj_kept tfibsegs B T_owed_counter_text (o_lyc cx) (o_Sc cx) (o_W cx) (o_memc cx) W3 m3 (spZ (o_regs cx)) (oc_E cx).
(* a segment from the symbolic state ss under INV reaches the contract's post *)
Definition oc_from (ss : sstate) (INV : occx -> env -> world tfibsegs -> (word -> option byte) -> Prop) : Prop :=
  forall cx E ly3 S3 W3 (ms3 : machine_state) md3,
  oc_pre cx -> oc_env cx E -> oc_st cx ly3 S3 W3 (ms_mem ms3) md3 -> INV cx E W3 (ms_mem ms3) ->
  st_ok tfibsegs E ss (restrict (w_H W3) ms3) ->
  SRr tfibsegs W3 (mkCfg ms3 md3) (oc_post cx).
End ctx.

(* ================================ the invariants ================================ *)
(* the first loop after i characters: n digits, s their patterns, dot the eight flags (codec_owe.ct1_owe) *)
Definition oc_ct (tb : list Z) (i n : nat) (s dot : list Z) : Prop :=
  (i < length tb)%nat /\ (forall j, (j < i)%nat -> nth j tb 0 <> 0) /\
  codec_owe.ct1_owe tb 0 [] (repeat 0 8) = codec_owe.ct1_owe (skipn i tb) (Z.of_nat n) s dot /\
  length s = n /\ codec_text.ct_inv (Z.of_nat n) dot /\ Forall (fun v => 0 <= v < 128) s /\
  Forall (fun d => d = 0 \/ d = 1) dot.
Definition oc_atoms_sd (E : env) (n : nat) (s dot : list Z) : Prop :=
  (forall k, (k < n)%nat -> ew E (310 + k) = Z_to_bv 64 (nth k s 0)) /\
  (forall k, (k < n)%nat -> ew E (320 + k) = Z_to_bv 64 (nth k dot 0)).
Definition INV_L (n fuel : nat) (cx : occx) (E : env) (W3 : world tfibsegs) (m3 : word -> option byte) : Prop :=
  exists i s dot, ew E 300 = Z_to_bv 64 (o_q cx + Z.of_nat i) /\ oc_atoms_sd E n s dot /\
  oc_ct (o_tb cx) i n s dot /\ (length (o_tb cx) - i <= fuel)%nat.
Definition INV_Z (n : nat) (cx : occx) (E : env) (W3 : world tfibsegs) (m3 : word -> option byte) : Prop :=
  exists s dot, oc_atoms_sd E n s dot /\
  codec_owe.ct1_owe (o_tb cx) 0 [] (repeat 0 8) = Some (Z.of_nat n, s, dot) /\
  length s = n /\ codec_text.ct_inv (Z.of_nat n) dot /\ Forall (fun v => 0 <= v < 128) s /\
  Forall (fun d => d = 0 \/ d = 1) dot.
(* the release with the literal z in a0: z is the return code; on success the digits and the dots are written *)
Definition INV_R (z : Z) (cx : occx) (E : env) (W3 : world tfibsegs) (m3 : word -> option byte) : Prop :=
  let '(r, s, d) := codec_owe.owed_counter_text_spec (o_tb cx) in
  Z_to_bv 64 z = w64 r /\
  (r = 0 -> garr8 tfibsegs (mrestrict (w_H W3) m3) (o_sg cx) s /\ val_mem tfibsegs (mrestrict (w_H W3) m3) (o_dt cx) 1 d).

Section fa. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
(* the frame and flag addresses of two journals over the same caller's journal agree (they read ly_F) *)
Lemma oc_fa_eq : forall B STK sp0 FP ly S (W0 : world tfibsegs) mem0 md0 own lyc Sc W memc mdc k own3 ly3 S3 W3 mem3 md3 k3,
  ajournal tfibsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  ajournal tfibsegs B STK sp0 FP ly S W0 mem0 md0 own3 ly3 S3 W3 mem3 md3 k3 ->
  (forall c p, frame_addr ly3 c p = frame_addr lyc c p) /\ (forall c p, flag_addr ly3 c p = flag_addr lyc c p).
Proof.
intros B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k own3 ly3 S3 W3 mem3 md3 k3 (_ & Hly & _) (_ & Hly3 & _).
destruct Hly as (_ & _ & _ & _ & _ & EF & _). destruct Hly3 as (_ & _ & _ & _ & _ & EF3 & _).
split; intros c p; unfold frame_addr, flag_addr; rewrite EF, EF3; reflexivity.
Qed.
End fa.
(* an atom's value is not changed by a havoc whose window misses it *)
Lemma oc_ew_out : forall E k ws n, ((n < k)%nat \/ (k + length ws <= n)%nat) -> ew (havoc E k ws) n = ew E n.
Proof. intros E k ws n [H | H]; [apply ew_havoc_old | apply ew_havoc_above]; exact H. Qed.
Lemma oc_agree_ewset : forall E0 E k v, env_agree 32 E0 E -> (32 <= k)%nat -> env_agree 32 E0 (ewset E k v).
Proof.
intros E0 E k v [H1 H2] Hk. split; [|exact H2]. intros n Hn. cbn [ew ewset].
destruct (Nat.eqb_spec n k) as [-> | Hne]; [lia | apply H1; exact Hn].
Qed.
Lemma oc_atoms_sd_havoc : forall E n s dot k ws, oc_atoms_sd E n s dot -> (n <= 8)%nat ->
  ((328 <= k)%nat \/ (k + length ws <= 310)%nat) -> oc_atoms_sd (havoc E k ws) n s dot.
Proof.
intros E n s dot k ws (H1 & H2) Hn Hk. split; intros j Hj; rewrite oc_ew_out by lia; [apply H1 | apply H2]; exact Hj.
Qed.

(* the shadow entries of the frame's two arrays (s[] = [F + 32, F + 40), dot[] = [F + 64, F + 96)): their shadow bytes
   read 0 in the frame's shadow region (atom 88), which the state HS holds *)
Section shf. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Lemma oc_shent_frame : forall E (W : world tfibsegs) (m : word -> option byte) F o n,
  ew E 75 = Z_to_bv 64 F -> ew E 32 = Z_to_bv 64 SB -> F mod 8 = 0 -> o mod 8 = 0 -> n mod 8 = 0 -> 0 <= o -> 0 < n ->
  4096 <= F -> amem_range (F + o) n -> F + o + n <= 2 ^ 63 ->
  (forall j, 0 <= j < n / 8 -> aview tfibsegs (w_H W) m (SB + F / 8 + o / 8 + j) = Some 0) ->
  shent_ok tfibsegs CW_Bx E (mrestrict (w_H W) m) (mkSHE 75 o (o + n)).
Proof.
intros E W m F o n E75 E32 HF Ho Hn Ho0 Hn0 HF4 Ham Hhi Hz.
apply (cw_shent_ra_off W m E 75 F o n); try lia; try assumption.
apply zero_shadow_of_bytes; [rewrite Zplus_mod, HF, Ho; reflexivity | exact Hn | lia |].
intros i Hi. rewrite <- SB_SHADOW_OFF.
replace ((F + o) / 8) with (F / 8 + o / 8).
- replace (SB + (F / 8 + o / 8) + i) with (SB + F / 8 + o / 8 + i) by lia. apply Hz. exact Hi.
- pose proof (Z.div_mod F 8 ltac:(lia)). pose proof (Z.div_mod o 8 ltac:(lia)).
  rewrite HF in *. rewrite Ho in *. rewrite Z.add_0_r in *.
  replace (F + o) with ((F / 8 + o / 8) * 8) by lia. rewrite Z.div_mul by lia. reflexivity.
Qed.
End shf.

(* ================================ the walk's reads of the caller's objects ================================ *)
(* a byte of the read-only window is a byte of the image (lib/A/Prog/check_personality_A_cut.v cp_ro_img) *)
Lemma oc_ro_img : forall a, in_roP tfibsegs CA_RLO CA_RHI a -> in_img tfibsegs a.
Proof.
intros a [(s & Hs & _ & Hr) | Hgot]; [exists s; split; [exact Hs | exact Hr]|].
unfold in_img. eexists. split; [right; right; left; reflexivity|].
match goal with |- Z.le ?lo a /\ Z.lt a (?lo' + ?sz) => let l := eval vm_compute in lo in let h := eval vm_compute in sz in
change lo with l; change sz with h end. unfold CA_RLO, CA_RHI in Hgot. lia.
Qed.
Section rd. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Variable MT : ameter_ops.
Variable GLYPHA : Z.
Variable ROSTRS : list (Z * Z).
(* the callee's image tables at a deeper window, in a later state (the read-only data kept by tcj_kept clause 3) *)
Lemma oc_cimg_at : forall cx ly3 S3 W3 m3 md3 sp' T',
  oc_pre B GLYPHA ROSTRS cx -> oc_st B MT cx ly3 S3 W3 m3 md3 ->
  sp' <= spZ (o_regs cx) -> spZ (o_regs cx) - T_owed_counter_text <= sp' - T' ->
  cimg_rd tfibsegs B CA_RLO CA_RHI W3 m3 sp' T' ((GLYPHA, 464) :: ROSTRS).
Proof.
intros cx ly3 S3 W3 m3 md3 sp' T' Hpre (_ & _ & _ & _ & _ & _ & (_ & _ & K3 & _)) H1 H2.
pose proof Hpre as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (HRO & HF) & _).
split.
- intros a Hro Ho He. rewrite (K3 a (oc_ro_img a Hro) Ho He). exact (HRO a Hro Ho He).
- eapply Forall_impl; [|exact HF]. intros [x n] (Hro & Hq0 & Hn0 & H63 & Ham & Hcw & Himg & Hus).
  split; [exact Hro|]. split; [exact Hq0|]. split; [exact Hn0|]. split; [exact H63|]. split; [exact Ham|].
  split; [unfold coff_win in *; cbn [fst snd] in *; lia|]. split; [exact Himg | exact Hus].
Qed.
(* the text's byte i and its shadow, in any later state the walk carries (oc_st): kept by tcj_kept (a block or a
   frame of the call state, off the bytes the call writes) *)
Lemma oc_text_at : forall cx ly3 S3 W3 m3 md3 i,
  oc_pre B GLYPHA ROSTRS cx -> oc_st B MT cx ly3 S3 W3 m3 md3 -> (i < length (o_tb cx))%nat ->
  aview tfibsegs (w_H W3) m3 (o_q cx + Z.of_nat i) = Some (nth i (o_tb cx) 0) /\ 0 <= nth i (o_tb cx) 0 < 256 /\
  range_addressable (aview tfibsegs (w_H W3) m3) SHADOW_OFF (o_q cx + Z.of_nat i) 1 /\
  amem_range (o_q cx) (oc_n cx) /\ 0 < o_q cx /\ o_q cx + oc_n cx <= 2 ^ 63 /\
  coff_win (spZ (o_regs cx)) T_owed_counter_text (o_q cx) (oc_n cx).
Proof.
intros cx ly3 S3 W3 m3 md3 i Hpre (HJ3 & Hfr & Hnin & HPm & _ & _ & (_ & K2 & _ & K4 & _)) Hi.
pose proof Hpre as (HE & _ & (Hq0 & Hg & _ & (_ & Hqn & _ & Hra & _ & Ham & Hcw)) & Hcq & _ & _ & Hdsg & _ & _ & _ & Hdt & _ & _ & Hdqs & Hdqd & _).
unfold oc_n in *. set (n := Z.of_nat (length (o_tb cx))) in *.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (Hg i Hi) as (Vi & Ri).
assert (Hamq : 0 <= o_q cx + Z.of_nat i < kHighMemEnd).
{ unfold amem_range in Ham. lia. }
assert (HnE : ~ oc_E cx (o_q cx + Z.of_nat i)).
{ unfold oc_E. intros [Hx | Hx]; [destruct Hdqs | destruct Hdqd]; lia. }
assert (Hent : aview tfibsegs (w_H (o_W cx)) (o_memc cx) (o_q cx + Z.of_nat i) = Some (nth i (o_tb cx) 0))
  by exact (aview_of_val_mem1 tfibsegs _ _ _ _ Vi Ri).
pose proof (proj1 HJ3) as HAR3.
(* the shadow byte of x is not a byte the call writes: it lies in the shadow band, the call's bytes in application memory *)
assert (HsE : forall x, 0 <= x < 2 ^ 47 -> ~ oc_E cx (shadow_of_addr SHADOW_OFF x)).
{ intros x Hx. pose proof Hdsg as (_ & _ & _ & _ & _ & _ & Hamg & _).
  assert (Hamd : amem_range (o_dt cx) 1) by (destruct Hdt as [((_ & _ & _ & _ & _ & _ & Hm & _) & _) | (_ & _ & _ & _ & _ & _ & _ & Hm & _)]; exact Hm).
  unfold oc_E, shadow_of_addr, amem_range in *. rewrite C3, C4, C5 in *.
  assert (0 <= x / 8 < 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  change SHADOW_OFF with 2147450880 in *. lia. }
destruct Hcq as [(b & m & Hin & Hb1 & Hb2) | (cid & pos & Hin & Hf1 & Hf2)].
- (* a block of the call state *)
  assert (Hin3 : In (b, m) (ablocks B ly3 S3)) by exact (Permutation_in _ (Permutation_sym HPm) Hin).
  split.
  { replace (o_q cx + Z.of_nat i) with (b + (o_q cx + Z.of_nat i - b)) by lia.
    rewrite (K2 b m (o_q cx + Z.of_nat i - b) Hin ltac:(lia) ltac:(replace (b + (o_q cx + Z.of_nat i - b)) with (o_q cx + Z.of_nat i) by lia; exact HnE)).
    replace (b + (o_q cx + Z.of_nat i - b)) with (o_q cx + Z.of_nat i) by lia. exact Hent. }
  split; [exact Ri|].
  split; [exact (range_addressable_of_block tfibsegs B LAWS ly3 S3 W3 m3 md3 b m (o_q cx + Z.of_nat i) 1 HAR3 Hin3 ltac:(lia) ltac:(lia))|].
  auto.
- (* a frame of the call state *)
  assert (Hzone : forall a, frame_addr (o_lyc cx) cid pos <= a < frame_addr (o_lyc cx) cid pos + fs_frame_bytes cid ->
    in_zr a (frame_rng (o_lyc cx) (cid, pos))) by (intros a Ha; unfold in_zr, frame_rng; cbn [fst snd]; lia).
  split.
  { rewrite (K4 cid pos (o_q cx + Z.of_nat i) Hin (or_introl (Hzone (o_q cx + Z.of_nat i) ltac:(lia))) HnE). exact Hent. }
  split; [exact Ri|].
  split; [|auto].
  apply (range_addressable_agree (aview tfibsegs (w_H (o_W cx)) (o_memc cx))).
  + intros x Hx. assert (Hx47 : 0 <= x < 2 ^ 47) by (unfold amem_range in Ham; rewrite C3, C4, C5 in Ham; lia).
    pose proof (proj1 (proj1 HE)) as HARe.
    destruct (frames_bounds tfibsegs B LAWS _ _ _ _ _ cid pos HARe Hin) as (Hf4096 & Hfceil & _).
    destruct (al_frames _ _ LAWS _ _ _ _ _ cid pos HARe Hin) as (Hfal & _).
    pose proof HARe as (Me & _).
    assert (Hcid : 0 <= cid) by (first [ destruct (YG0s.frame_facts _ _ _ _ _ _ Me Hin) as (Hc & _); lia
                                       | destruct (YG0s.frame_facts _ _ _ _ _ _ _ Me Hin) as (Hc & _); lia
                                       | destruct (YG0s.frame_facts _ _ _ _ _ _ _ _ Me Hin) as (Hc & _); lia ]).
    assert (Hb8 : fs_frame_bytes cid mod 8 = 0).
    { unfold fs_frame_bytes. rewrite Z.shiftl_mul_pow2 by lia.
      replace (64 * 2 ^ cid) with ((8 * 2 ^ cid) * 8) by lia. apply Z_mod_mult. }
    assert (Hf8 : frame_addr (o_lyc cx) cid pos mod 8 = 0).
    { pose proof (Z.div_mod (frame_addr (o_lyc cx) cid pos) 32 ltac:(lia)) as D. rewrite Hfal, Z.add_0_r in D.
      rewrite D. replace (32 * (frame_addr (o_lyc cx) cid pos / 32)) with ((4 * (frame_addr (o_lyc cx) cid pos / 32)) * 8) by lia.
      apply Z_mod_mult. }
    set (f := frame_addr (o_lyc cx) cid pos) in *. set (bs := fs_frame_bytes cid) in *.
    pose proof (Z.div_mod f 8 ltac:(lia)) as Df. pose proof (Z.div_mod bs 8 ltac:(lia)) as Db.
    assert (Hq : f / 8 <= x / 8) by (apply Z.div_le_mono; lia).
    assert (Hq2 : x / 8 < f / 8 + bs / 8) by (apply Z.div_lt_upper_bound; lia).
    apply (K4 cid pos _ Hin); [right | exact (HsE x Hx47)].
    unfold in_zr, shadow_of_addr, shadow_addr. cbn [fst snd]. subst f bs. lia.
  + apply (range_addressable_sub _ _ (o_q cx) n); [exact Hra | lia | lia].
Qed.
End rd.

(* the callee's image tables from the walk's kept invariant (oc_cimg_at without the rest of oc_st) *)
Section ck. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable GLYPHA : Z.
Variable ROSTRS : list (Z * Z).
Lemma oc_cimg_kt : forall cx (W3 : world tfibsegs) m3 sp T E sp' T',
  oc_pre B GLYPHA ROSTRS cx ->
  tcj_kept tfibsegs B T (o_lyc cx) (o_Sc cx) (o_W cx) (o_memc cx) W3 m3 sp E ->
  sp' <= spZ (o_regs cx) -> spZ (o_regs cx) - T_owed_counter_text <= sp' - T' ->
  cimg_rd tfibsegs B CA_RLO CA_RHI W3 m3 sp' T' ((GLYPHA, 464) :: ROSTRS).
Proof.
intros cx W3 m3 sp T E sp' T' Hpre (_ & _ & K3 & _) H1 H2.
pose proof Hpre as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (HRO & HF) & _).
split.
- intros a Hro Ho He. rewrite (K3 a (oc_ro_img a Hro) Ho He). exact (HRO a Hro Ho He).
- eapply Forall_impl; [|exact HF]. intros [x n] (Hro & Hq0 & Hn0 & H63 & Ham & Hcw & Himg & Hus).
  split; [exact Hro|]. split; [exact Hq0|]. split; [exact Hn0|]. split; [exact H63|]. split; [exact Ham|].
  split; [unfold coff_win in *; cbn [fst snd] in *; lia|]. split; [exact Himg | exact Hus].
Qed.
End ck.

(* ================================ the first loop's steps, on the plain spec ================================ *)
Lemma oc_atoms_sd_havoc2 : forall E n s dot k ws, oc_atoms_sd E n s dot ->
  (forall j, (j < n)%nat -> ((310 + j < k)%nat \/ (k + length ws <= 310 + j)%nat) /\ ((320 + j < k)%nat \/ (k + length ws <= 320 + j)%nat)) ->
  oc_atoms_sd (havoc E k ws) n s dot.
Proof.
intros E n s dot k ws (H1 & H2) Hk. split; intros j Hj; destruct (Hk j Hj) as (Ha & Hb).
- rewrite oc_ew_out by lia. apply H1. exact Hj.
- rewrite oc_ew_out by lia. apply H2. exact Hj.
Qed.
Lemma oc_in0_after : forall (tb : list Z) i, In 0 tb -> (forall j, (j < i)%nat -> nth j tb 0 <> 0) -> nth i tb 0 <> 0 ->
  (S i < length tb)%nat.
Proof.
intros tb i Hin Hnz Hi. destruct (In_nth tb 0 0 Hin) as (k & Hk & Hk0).
destruct (Nat.lt_ge_cases k (S i)) as [Hlt | Hge].
- destruct (Nat.eq_dec k i) as [-> | Hne]; [exfalso; exact (Hi Hk0) | exfalso; exact (Hnz k ltac:(lia) Hk0)].
- destruct (Nat.eq_dec k (S i)) as [-> | Hne]; [exact Hk | lia].
Qed.
Lemma oc_Forall_upd : forall (P : Z -> Prop) l i v, Forall P l -> P v -> Forall P (DgnLib.upd_at l i v).
Proof.
intros P l i v Hl Hv. unfold DgnLib.upd_at.
assert (HF : forall k (l0 : list Z), Forall P l0 -> Forall P (firstn k l0))
  by (induction k as [|k IH]; intros [|x l0] H; cbn; auto; inversion H; subst; constructor; auto).
assert (HS : forall k (l0 : list Z), Forall P l0 -> Forall P (skipn k l0))
  by (induction k as [|k IH]; intros [|x l0] H; cbn; auto; inversion H; subst; auto).
apply Forall_app. split; [apply HF; exact Hl|]. constructor; [exact Hv | apply HS; exact Hl].
Qed.
Lemma oc_ct1_cons : forall ch t n s dot, codec_owe.ct1_owe (ch :: t) n s dot =
  if ch =? 0 then Some (n, s, dot)
  else if (ch =? 0x2e) && (0 <? n) && (nth (Z.to_nat (n - 1)) dot 0 =? 0)
  then codec_owe.ct1_owe t n s (DgnLib.upd_at dot (n - 1) 1)
  else if (codec_owe.owed_seg7_spec (if ch =? 0x2e then 0x20 else ch) <? 0) || (n =? 8) then None
  else codec_owe.ct1_owe t (n + 1) (s ++ [codec_owe.owed_seg7_spec (if ch =? 0x2e then 0x20 else ch)])
         (DgnLib.upd_at dot n (if ch =? 0x2e then 1 else 0)).
Proof. reflexivity. Qed.
Lemma oc_step_end : forall tb i n s dot, oc_ct tb i n s dot -> nth i tb 0 = 0 ->
  codec_owe.ct1_owe tb 0 [] (repeat 0 8) = Some (Z.of_nat n, s, dot).
Proof.
intros tb i n s dot (Hi & _ & Hsp & _) H0. rewrite Hsp, (codec_text.skipn_cons_nth tb i 0 Hi), H0, oc_ct1_cons. reflexivity.
Qed.
Lemma oc_step_merge : forall tb i n s dot, oc_ct tb i n s dot -> In 0 tb -> nth i tb 0 = 46 -> (0 < n)%nat ->
  nth (n - 1) dot 0 = 0 -> oc_ct tb (S i) n s (DgnLib.upd_at dot (Z.of_nat n - 1) 1).
Proof.
intros tb i n s dot (Hi & Hnz & Hsp & Hl & Hinv & Hs & Hd) Hin Hc Hn Hdot.
split; [apply (oc_in0_after tb i Hin Hnz); lia|].
split; [intros j Hj; destruct (Nat.eq_dec j i) as [-> | Hne]; [lia | apply Hnz; lia]|].
split.
{ rewrite Hsp, (codec_text.skipn_cons_nth tb i 0 Hi), Hc, oc_ct1_cons.
  replace (Z.to_nat (Z.of_nat n - 1)) with (n - 1)%nat by lia. rewrite Hdot.
  replace (0 <? Z.of_nat n) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
split; [exact Hl|]. split; [apply codec_text.ct_inv_dot; [exact Hinv | lia]|]. split; [exact Hs|].
apply oc_Forall_upd; [exact Hd | right; reflexivity].
Qed.
Lemma oc_merge_false : forall c n dot, ~ (c = 46 /\ (0 < n)%nat /\ nth (n - 1) dot 0 = 0) ->
  ((c =? 0x2e) && (0 <? Z.of_nat n) && (nth (Z.to_nat (Z.of_nat n - 1)) dot 0 =? 0)) = false.
Proof.
intros c n dot H. destruct (Z.eqb_spec c 0x2e) as [Hc | Hc]; [|reflexivity].
destruct (Z.ltb_spec 0 (Z.of_nat n)) as [Hn | Hn]; [|reflexivity].
replace (Z.to_nat (Z.of_nat n - 1)) with (n - 1)%nat by lia.
destruct (Z.eqb_spec (nth (n - 1) dot 0) 0) as [Hd | Hd]; [|reflexivity].
exfalso. apply H. split; [exact Hc|]. split; [lia | exact Hd].
Qed.
Lemma oc_step_call : forall tb i n s dot c, oc_ct tb i n s dot -> In 0 tb -> nth i tb 0 = c -> c <> 0 ->
  ~ (c = 46 /\ (0 < n)%nat /\ nth (n - 1) dot 0 = 0) ->
  0 <= codec_owe.owed_seg7_spec (if c =? 46 then 32 else c) -> (n < 8)%nat ->
  oc_ct tb (S i) (S n) (s ++ [codec_owe.owed_seg7_spec (if c =? 46 then 32 else c)])
    (DgnLib.upd_at dot (Z.of_nat n) (if c =? 46 then 1 else 0)).
Proof.
intros tb i n s dot c (Hi & Hnz & Hsp & Hl & Hinv & Hs & Hd) Hin Hc Hc0 Hm Hv Hn8.
split; [apply (oc_in0_after tb i Hin Hnz); lia|].
split; [intros j Hj; destruct (Nat.eq_dec j i) as [-> | Hne]; [lia | apply Hnz; lia]|].
split.
{ rewrite Hsp, (codec_text.skipn_cons_nth tb i 0 Hi), Hc, oc_ct1_cons.
  rewrite (proj2 (Z.eqb_neq c 0) Hc0), (oc_merge_false c n dot Hm).
  replace ((codec_owe.owed_seg7_spec (if c =? 46 then 32 else c) <? 0) || (Z.of_nat n =? 8)) with false
    by (symmetry; apply orb_false_iff; split; [apply Z.ltb_ge; lia | apply Z.eqb_neq; lia]).
  replace (Z.of_nat (S n)) with (Z.of_nat n + 1) by lia. reflexivity. }
split; [rewrite length_app, Hl; cbn; lia|].
split; [replace (Z.of_nat (S n)) with (Z.of_nat n + 1) by lia; apply codec_text.ct_inv_next; [exact Hinv | lia]|].
split.
{ apply Forall_app. split; [exact Hs|]. constructor; [|constructor].
  destruct (codec_text.owed_seg7_range (if c =? 46 then 32 else c)) as [E | E]; lia. }
apply oc_Forall_upd; [exact Hd|]. destruct (c =? 46); [right | left]; reflexivity.
Qed.
Lemma oc_step_err : forall tb i n s dot c, oc_ct tb i n s dot -> nth i tb 0 = c -> c <> 0 ->
  ~ (c = 46 /\ (0 < n)%nat /\ nth (n - 1) dot 0 = 0) ->
  (codec_owe.owed_seg7_spec (if c =? 46 then 32 else c) < 0 \/ n = 8%nat) ->
  codec_owe.owed_counter_text_spec tb = (DgnSpec.E_RANGE, [], 0).
Proof.
intros tb i n s dot c (Hi & Hnz & Hsp & _) Hc Hc0 Hm Hv.
unfold codec_owe.owed_counter_text_spec.
rewrite Hsp, (codec_text.skipn_cons_nth tb i 0 Hi), Hc, oc_ct1_cons.
rewrite (proj2 (Z.eqb_neq c 0) Hc0), (oc_merge_false c n dot Hm).
replace ((codec_owe.owed_seg7_spec (if c =? 46 then 32 else c) <? 0) || (Z.of_nat n =? 8)) with true.
- reflexivity.
- symmetry. apply orb_true_iff. destruct Hv as [Hv | ->]; [left; apply Z.ltb_lt; exact Hv | right; reflexivity].
Qed.

Lemma oc_atoms_sd_ewset : forall E n s dot k v, oc_atoms_sd E n s dot ->
  (forall j, (j < n)%nat -> 310 + j <> k /\ 320 + j <> k)%nat -> oc_atoms_sd (ewset E k v) n s dot.
Proof.
intros E n s dot k v (H1 & H2) Hk. split; intros j Hj; destruct (Hk j Hj) as (Ha & Hb);
rewrite ew_ewset_other by lia; [apply H1 | apply H2]; exact Hj.
Qed.
(* the digit atoms carried from the environment of Hsd to Et, through Et's havoc / ewset layers *)
Ltac oc_sd_to Et :=
  lazymatch goal with Hsd : oc_atoms_sd ?Eh ?n ?s ?d |- _ =>
  lazymatch Et with
  | Eh => idtac
  | havoc ?E1 ?k ?ws => oc_sd_to E1; apply (oc_atoms_sd_havoc2 _ _ _ _ k ws) in Hsd; [| intros ? ?; cbn [length]; lia]
  | ewset ?E1 ?k ?v => oc_sd_to E1; apply (oc_atoms_sd_ewset _ _ _ _ k v) in Hsd; [| intros ? ?; lia]
  end end.

(* HAE and the atom facts carried to the state's current environment (its havoc / ewset layers over theirs) *)
Ltac oc_cur :=
  lazymatch goal with HS : st_ok _ ?Et _ _ |- _ =>
  lazymatch goal with HAE : env_agree 32 ?E0 ?Eb |- _ =>
    let H2 := fresh "HAE" in
    assert (H2 : env_agree 32 E0 Et)
      by (repeat match goal with
          | |- env_agree 32 _ Eb => exact HAE
          | |- env_agree 32 _ (havoc _ _ _) => apply env_agree_havoc_ge; [cbv; lia|]
          | |- env_agree 32 _ (ewset _ _ _) => apply oc_agree_ewset; [|cbv; lia]
          end);
    clear HAE; rename H2 into HAE end;
  repeat match goal with
  | H : ew ?Eo ?n = ?v |- _ =>
    lazymatch Eo with Et => fail | _ => idtac end;
    let H2 := fresh in
    assert (H2 : ew Et n = v)
      by (repeat (first [rewrite oc_ew_out by (cbn [length]; lia) | rewrite ew_ewset_other by lia]); exact H);
    clear H; rename H2 into H
  | H : bv_unsigned (ew ?Eo ?n) = ?v |- _ =>
    lazymatch Eo with Et => fail | _ => idtac end;
    let H2 := fresh in
    assert (H2 : bv_unsigned (ew Et n) = v)
      by (repeat (first [rewrite oc_ew_out by (cbn [length]; lia) | rewrite ew_ewset_other by lia]); exact H);
    clear H; rename H2 into H
  end end.

(* the token engine's ewset layers dropped from the state's environment: the registers that use their atoms put in
   literals, then each layer removed (the state does not use its atom) *)
Section dew. Context {fx : YK11.FPState}.
Lemma oc_drop_ewset : forall E ss ms k v, st_ok tfibsegs (ewset E k v) ss ms ->
  ss_atoms_on (fun n => negb (Nat.eqb n k)) ss = true -> st_ok tfibsegs E ss ms.
Proof.
intros E ss ms k v HS Ha. eapply (st_ok_agree_on tfibsegs (fun n => negb (Nat.eqb n k))); [exact HS | | exact Ha].
split; [|reflexivity]. intros n Hn. cbn [ew ewset]. apply negb_true_iff in Hn. rewrite Hn. reflexivity.
Qed.
End dew.
Ltac oc_keys Et := lazymatch Et with ewset ?E1 ?k _ => let r := oc_keys E1 in constr:(k :: r) | _ => constr:(@nil nat) end.
Ltac oc_unewset :=
  lazymatch goal with HS : st_ok _ ?Et ?ssx _ |- _ =>
  let ks := oc_keys Et in
  let rl := eval vm_compute in (oc_regs_using (ss_regs ssx) ks 0) in
  oc_lit_regs HS rl;
  repeat lazymatch goal with HS2 : st_ok _ (ewset ?E1 ?k1 ?v1) ?ss1 ?ms1 |- _ =>
    let HS3 := fresh "HS3" in
    pose proof (oc_drop_ewset E1 ss1 ms1 k1 v1 HS2 ltac:(vm_compute; reflexivity)) as HS3; clear HS2; rename HS3 into HS end
  end.

(* the digit atoms' facts one by one (cpw_rebase carries `ew Ev n = v` facts, not oc_atoms_sd), and back *)
Ltac oc_sd_split_rec Hs1 Hd1 k n :=
  lazymatch eval cbv in (Nat.ltb k n) with
  | true =>
    let A := fresh "Es" in let D := fresh "Ed" in
    pose proof (Hs1 k ltac:(lia)) as A; pose proof (Hd1 k ltac:(lia)) as D;
    let a := eval cbv in (310 + k)%nat in let d := eval cbv in (320 + k)%nat in
    change (310 + k)%nat with a in A; change (320 + k)%nat with d in D;
    oc_sd_split_rec Hs1 Hd1 (S k) n
  | false => idtac
  end.
Ltac oc_sd_split :=
  lazymatch goal with Hsd : oc_atoms_sd ?E ?n ?s ?d |- _ =>
    let Hs1 := fresh "Hs1" in let Hd1 := fresh "Hd1" in
    destruct Hsd as [Hs1 Hd1]; oc_sd_split_rec Hs1 Hd1 0%nat n; clear Hs1 Hd1 end.
(* oc_atoms_sd at the current environment Ej from the carried facts (peeling Ej's havoc / ewset layers) *)
Ltac oc_ew_peel := repeat (first [rewrite oc_ew_out by (cbn [length]; lia) | rewrite ew_ewset_other by lia]).


(* bltz on a register holding the 64-bit pattern of v *)
Lemma oc_bltz : forall E n v, ew E n = Z_to_bv 64 v -> - 2 ^ 63 <= v < 2 ^ 63 ->
  branch_taken BC_LT (sv_denot E (SOff n 0)) (sv_denot E (SLit 0)) = (v <? 0).
Proof.
intros E n v Hn Hv. rewrite YO0c.branch_lt. cbn [sv_denot]. rewrite Hn, Z.add_0_r, Z_to_bv_bv_unsigned.
rewrite !unsigned_lit. unfold zcanon, M64, YO0b.s64. change (0 mod 2 ^ 64) with 0. change (0 <? 2 ^ 63) with true.
destruct (Z.ltb_spec v 0) as [Hl | Hl].
- rewrite <- (Z.mod_add v 1 (2 ^ 64)) by lia. rewrite Z.mod_small by lia.
  destruct (Z.ltb_spec (v + 1 * 2 ^ 64) (2 ^ 63)); [lia|]. apply Z.ltb_lt. lia.
- rewrite Z.mod_small by lia. destruct (Z.ltb_spec v (2 ^ 63)); [|lia]. apply Z.ltb_ge. lia.
Qed.
Lemma oc_nth_app_l : forall (s : list Z) v k, (k < length s)%nat -> nth k (s ++ [v]) 0 = nth k s 0.
Proof. intros. apply app_nth1. exact H. Qed.
Lemma oc_nth_app_r : forall (s : list Z) v k, length s = k -> nth k (s ++ [v]) 0 = v.
Proof. intros s v k H. rewrite app_nth2 by lia. rewrite H, Nat.sub_diag. reflexivity. Qed.
Lemma oc_nth_upd_same : forall (l : list Z) i x, (Z.to_nat i < length l)%nat -> nth (Z.to_nat i) (DgnLib.upd_at l i x) 0 = x.
Proof.
intros l i x H. unfold DgnLib.upd_at. rewrite app_nth2; rewrite length_firstn; [|lia].
replace (Z.to_nat i - Init.Nat.min (Z.to_nat i) (length l))%nat with 0%nat by lia. reflexivity.
Qed.


Ltac oc_sd_leaf :=
  first [ assumption
        | rewrite oc_nth_app_l by lia; oc_sd_leaf
        | rewrite oc_nth_app_r by lia; assumption
        | rewrite codec_text.nth_upd_other by lia; assumption
        | lazymatch goal with |- _ = Z_to_bv 64 (nth ?j (DgnLib.upd_at ?l ?i ?x) 0) =>
            replace (nth j (DgnLib.upd_at l i x) 0) with x by (symmetry; apply (oc_nth_upd_same l i x); lia);
            first [assumption | rewrite oc_ew_havoc1; reflexivity] end ].
Ltac oc_sd_cases kk :=
  first [ exfalso; lia
        | destruct kk as [|kk]; [cbn [Nat.add]; oc_ew_peel; oc_sd_leaf | oc_sd_cases kk] ].
Ltac oc_sd_build :=
  lazymatch goal with |- oc_atoms_sd ?Ej ?n ?s ?d =>
    split; let kk := fresh "kk" in let Hk := fresh "Hk" in intros kk Hk; oc_sd_cases kk end.

(* seqz (s9 - '.') on the text byte c *)
Lemma oc_seqz46 : forall E c, ew E 350 = Z_to_bv 64 c -> 0 <= c < 256 ->
  alu64 ALU_SLTU (Z_to_bv 64 (bv_unsigned (ew E 350) + -46)) (Z_to_bv 64 1) = Z_to_bv 64 (if c =? 46 then 1 else 0).
Proof.
intros E c H Hc. apply bv_eq. rewrite YO0c.seqz_unsigned, H. rewrite (unsigned_lit_small c) by lia. rewrite unsigned_lit.
unfold zcanon, M64. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
destruct (Z.eqb_spec c 46) as [-> | Hne].
- reflexivity.
- rewrite (Z.mod_small 0) by lia.
  replace ((c + -46) mod 2 ^ 64 =? 0) with false; [reflexivity|].
  symmetry. apply Z.eqb_neq. intros Hm.
  destruct (Z_lt_le_dec c 46).
  + rewrite <- (Z.mod_add (c + -46) 1 (2 ^ 64)) in Hm by lia. rewrite Z.mod_small in Hm by lia. lia.
  + rewrite Z.mod_small in Hm by lia. lia.
Qed.

(* CPgWalkCall.cpw_rebase for a havoc window [K, K + n) that may lie below other atoms of the state: the facts on
   atoms outside the window are carried (oc_ew_out) *)
Ltac oc_rebase :=
lazymatch goal with
| HS : st_ok tfibsegs (havoc ?Ev ?K ?ws) _ (restrict (w_H ?Wc) ?ms), HAE : env_agree 32 (Ereg ?regs ?xs) ?Ev |- _ =>
let E' := fresh "E" in let HEv := fresh "HEv" in
remember (havoc Ev K ws) as E' eqn:HEv in *;
let HAE2 := fresh "HAE" in
assert (HAE2 : env_agree 32 (Ereg regs xs) E') by (rewrite HEv; apply env_agree_havoc_ge; [cbv; lia | exact HAE]);
clear HAE; rename HAE2 into HAE;
repeat match goal with
| H : ew Ev ?n = ?v |- _ =>
  let H2 := fresh in
  first [ assert (H2 : ew E' n = v) by (rewrite HEv, oc_ew_out by (cbn [length]; lia); exact H); clear H; rename H2 into H
        | clear H ]
| H : bv_unsigned (ew Ev ?n) = ?v |- _ =>
  let H2 := fresh in
  first [ assert (H2 : bv_unsigned (ew E' n) = v) by (rewrite HEv, oc_ew_out by (cbn [length]; lia); exact H); clear H; rename H2 into H
        | clear H ]
end;
clear HEv;
repeat match goal with SH : sh_ok _ _ _ Ev _ |- _ => clear SH end;
assert (SHOK : sh_ok tfibsegs CW_Bx [] E' (mrestrict (w_H Wc) (ms_mem ms))) by constructor;
try clear Ev
end.

(* the sign-extended 32-bit load of a small atom value *)
Lemma oc_U_sx_small : forall E n d, ew E n = Z_to_bv 64 d -> 0 <= d < 2 ^ 31 -> U E (SExt true 32 (SOff n 0)) = d.
Proof.
intros E n d Hn Hd. rewrite U_SExt. cbv iota beta. rewrite (U_atom E n d Hn) by lia.
change (2 ^ Z.of_N 32) with (2 ^ 32). rewrite (Z.mod_small d) by lia.
unfold zcanon, M64, bv_swrap, bv_wrap.
replace (bv_half_modulus 32) with (2 ^ 31) by reflexivity. replace (bv_modulus 32) with (2 ^ 32) by reflexivity.
rewrite (Z.mod_small (d + 2 ^ 31)) by lia. replace (d + 2 ^ 31 - 2 ^ 31) with d by lia. apply Z.mod_small. lia.
Qed.

(* the dot flag dot[k] tested by `beqz` after `lw` (Hd), as a test on its value *)
Ltac oc_dot_hd Hd k :=
  rewrite branch_eq_U in Hd;
  lazymatch type of Hd with context [U ?Ecur (SExt true 32 (SOff k 0))] =>
    lazymatch goal with Edk : ew ?Eo k = Z_to_bv 64 ?d, Hd01x : Forall (fun d0 => d0 = 0 \/ d0 = 1) ?dl |- _ =>
    let Hx := fresh in let Hr := fresh in
    assert (Hx : ew Ecur k = Z_to_bv 64 d) by (oc_ew_peel; exact Edk);
    assert (Hr : d = 0 \/ d = 1) by (apply (codec_text.nth_Forall (fun d0 => d0 = 0 \/ d0 = 1)); [exact Hd01x | left; reflexivity]);
    rewrite (oc_U_sx_small Ecur k d Hx ltac:(lia)) in Hd; clear Hx Hr end end;
  rewrite U_lit in Hd by lia.
