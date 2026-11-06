(* rule 24: proves no function (kind: segment lemma of check_round_trip's walk, PORTED from a working branch
   d25a984c903 proofs/omx-clap-core/fuzz_state/lib/A/Prog/check_round_trip_stdefs.v St17 :521 / St18 :535 and
   check_round_trip_sd16.v :541, the bespoke ASan proof of THIS function on THESE bytes).

   check_round_trip 0x81a9c, fs.asan (image tfibsegs, the pinned fuzz_state.asan sha256 64b53ff86172bb07...), lane D1,
   the TWO fuzz_free crossings:
     segment 32  0x82298 (`bnez a0` not taken, bcmp returned 0) .. jal fuzz_free (got)  at 0x822a0, return 0x822a4
     segment 33  0x822a4 ..                                        jal fuzz_free (file) at 0x822a8, return 0x822ac
   Both enter fuzz_free at A_fuzz_free with a0 a live reader block whose head is in U, and both are instances of ONE
   generic crossing, crtD1_free_hcall: the lane's three fuzz_free entries (from crtD1_INV_82298 with got at atom 23,
   from crtD1_INV_822a4 with file at atom 22, and the empty-body arm of segment 31, which reaches the same call of
   fuzz_free (got) from 0x82274 with got at atom 10) differ only in WHICH pair of the boundary's extra block list X is
   freed. crtD1_H is that shared shape: the walk's four fixed blocks (text, want, same, back), the two trees and their
   blocks, and the list X of the reader blocks the lane's frees are still to take; a crossing turns
   X = X1 ++ (p, n) :: X2 into X1 ++ X2 and g_live into live - n, costs EV_fuzz_free ticks and no g_count bump, and
   gives back exactly n + HEAD block bytes.
   The engine work is the shared crossing of lib/A/FSH_crt_site.v (crt_seg_call / crt_seg_call_br) over this file's own
   measured runs from crt_ss2. The callee contract is FSH_Fn_alloc.fuzz_free_spec on its p <> 0 arm, the separation
   facts are a Theorem Labs lane's lib/A/FSH_crt_segD1_keep.v (crtD1_not_entry, crtD1_free_fp_clear), and the transport of the
   boundary's data facts across the callee's journal is FSW_rd's *_kept_call family. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0n YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YG05 YG0s YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import
AB1v AB1w FSupoison FSupoisonU FSH_YC20 FSH_Gen FSH_Base FSH_Rt FSPstat FSW_K FSW_K3 FSW_rres FSW_ret FSW_frame
FSW_rd FSW_strkit FSW_crt_tbl FSH_Fn_reader FSH_Fn_writer FSH_Fn_alloc FSH_Fn_crt FSH_crt_base
FSH_crt_site FSH_crt_segD1_inv FSH_crt_segD1_keep FSH_crt_segD1.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require WriterSpec HState PjStruct
  check_round_trip_stages_b.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require PjTree.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* SINK GUARD: a SUCCESS here (the build errors naming this line) means a wrong sink instance resolved. *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.

(* ================= the two measured runs (store-free, from the shared crt_ss2) ================= *)
(* segment 33: 0x822a4 .. the entry of fuzz_free with ra = 0x822ac and a0 = s6 (atom 22) *)
Definition crtD1F_sc33 : sstate :=
  Eval vm_compute in fst (sym_run_toN tfibsegs crt_tbl FUEL A_fuzz_free (crt_ss2 0x822a4)).
Lemma crtD1F_run33 :
  sym_run_toN tfibsegs crt_tbl FUEL A_fuzz_free (crt_ss2 0x822a4) = (crtD1F_sc33, RS_running).
Proof. vm_compute. reflexivity. Qed.
Lemma crtD1F_site33 : crt_csite crtD1F_sc33 A_fuzz_free 0x822ac.
Proof. unfold crt_csite. repeat split; vm_compute; reflexivity. Qed.
Lemma crtD1F_a0_33 : sr_get (ss_regs crtD1F_sc33) 10%bv = SOff 22 0.
Proof. vm_compute. reflexivity. Qed.
Lemma crtD1F_ra_33 : sr_get (ss_regs crtD1F_sc33) 1%bv = SLit 0x822ac.
Proof. vm_compute. reflexivity. Qed.
Lemma crtD1F_ssave33 : crt_ssave crtD1F_sc33.
Proof. apply crt_ssave_dec. vm_compute. reflexivity. Qed.

(* segment 32: 0x82298, the `bnez a0` of the bcmp answer (not taken, a0 = 0), then the call of fuzz_free (got) with
   ra = 0x822a4 and a0 = s7 (atom 23) *)
Definition crtD1F_sb32 : sstate := Eval vm_compute in fst (sym_runN tfibsegs crt_tbl FUEL (crt_ss2 0x82298)).
Lemma crtD1F_br32 :
  sym_runN tfibsegs crt_tbl FUEL (crt_ss2 0x82298) = (crtD1F_sb32, RS_stopped (SR_branch BC_NE (SOff 10 0) (SLit 0))).
Proof. vm_compute. reflexivity. Qed.
Definition crtD1F_sc32 : sstate :=
  Eval vm_compute in fst (sym_run_toN tfibsegs crt_tbl FUEL A_fuzz_free (add_cond crtD1F_sb32 crt_c0)).
Lemma crtD1F_run32 :
  sym_run_toN tfibsegs crt_tbl FUEL A_fuzz_free (add_cond crtD1F_sb32 crt_c0) = (crtD1F_sc32, RS_running).
Proof. vm_compute. reflexivity. Qed.
Lemma crtD1F_site32 : crt_site crtD1F_sb32 crtD1F_sc32 A_fuzz_free 0x822a4.
Proof. unfold crt_site, crt_csite. repeat split; vm_compute; reflexivity. Qed.
Lemma crtD1F_a0_32 : sr_get (ss_regs crtD1F_sc32) 10%bv = SOff 23 0.
Proof. vm_compute. reflexivity. Qed.
Lemma crtD1F_ra_32 : sr_get (ss_regs crtD1F_sc32) 1%bv = SLit 0x822a4.
Proof. vm_compute. reflexivity. Qed.
Lemma crtD1F_ssave32 : crt_ssave crtD1F_sc32.
Proof. apply crt_ssave_dec. vm_compute. reflexivity. Qed.

(* the callee's window fits crt's journal window, and the two return addresses are even and in range *)
Lemma crtD1F_stk : 0 <= STK_fuzz_free /\ STK_fuzz_free + 208 <= STK_check_round_trip.
Proof. split; (apply Z.leb_le; vm_compute; reflexivity). Qed.
Lemma crtD1F_r_ok : forall r : Z, r = 0x822a4 \/ r = 0x822ac -> 4096 <= r < 2 ^ 64 /\ r mod 2 = 0.
Proof.
intros r Hr. assert (H64 : 2 ^ 64 = 18446744073709551616) by (vm_compute; reflexivity).
rewrite H64. destruct Hr as [-> | ->]; (split; [lia | reflexivity]).
Qed.

(* ---- the 5-bit register index of a callee-saved slot ---- *)
Lemma crtD1F_bv5 : forall z, 0 <= z < 32 -> bv_unsigned (Z_to_bv 5 z) = z.
Proof.
intros z Hz. assert (H32 : bv_modulus 5 = 32) by (vm_compute; reflexivity).
rewrite Z_to_bv_unsigned. apply bv_wrap_small. rewrite H32. exact Hz.
Qed.

(* ---- the list algebra of peeling one pair out of the boundary's block / head lists ---- *)
Lemma crtD1F_rdh_app : forall l1 l2, rd_hblocks (l1 ++ l2) = rd_hblocks l1 ++ rd_hblocks l2.
Proof. intros l1 l2. unfold rd_hblocks. apply map_app. Qed.
Lemma crtD1F_rdhd_app : forall l1 l2, rd_heads (l1 ++ l2) = rd_heads l1 ++ rd_heads l2.
Proof. intros l1 l2. unfold rd_heads. apply map_app. Qed.
Lemma crtD1F_split : forall (A0 L4 Y1 Y2 D : list (Z * Z)) (x : Z * Z),
  A0 ++ L4 ++ (Y1 ++ x :: Y2) ++ D = (A0 ++ L4 ++ Y1) ++ x :: (Y2 ++ D).
Proof. intros. rewrite <- !app_assoc. reflexivity. Qed.
Lemma crtD1F_join : forall (A0 L4 Y1 Y2 D : list (Z * Z)),
  (A0 ++ L4 ++ Y1) ++ (Y2 ++ D) = A0 ++ L4 ++ (Y1 ++ Y2) ++ D.
Proof. intros. rewrite <- !app_assoc. reflexivity. Qed.
Lemma crtD1F_cons_app : forall (L1 L2 : list (Z * Z)) (x : Z * Z), L1 ++ x :: L2 = (L1 ++ [x]) ++ L2.
Proof. intros. rewrite <- app_assoc. reflexivity. Qed.
Lemma crtD1F_rdh_split : forall (Y1 Y2 : list (Z * Z)) (p n : Z),
  rd_hblocks (Y1 ++ (p, n) :: Y2) = rd_hblocks Y1 ++ (p - HEAD, n + HEAD) :: rd_hblocks Y2.
Proof. intros. unfold rd_hblocks. rewrite map_app. reflexivity. Qed.
Lemma crtD1F_rdhd_split : forall (Y1 Y2 : list (Z * Z)) (p n : Z),
  rd_heads (Y1 ++ (p, n) :: Y2) = rd_heads Y1 ++ (p - HEAD, HEAD) :: rd_heads Y2.
Proof. intros. unfold rd_heads. rewrite map_app. reflexivity. Qed.
Lemma crtD1F_rds0 : rd_sum [] = 0.
Proof. reflexivity. Qed.
Lemma crtD1F_rds1 : forall p n : Z, rd_sum [(p, n)] = n.
Proof. intros. unfold rd_sum. cbn [fold_right snd]. lia. Qed.
Lemma crtD1F_rds2 : forall p n q m : Z, rd_sum [(p, n); (q, m)] = n + m.
Proof. intros. unfold rd_sum. cbn [fold_right snd]. lia. Qed.

(* ---- the walk's four fixed blocks and two fixed heads at the fuzz_free boundaries ---- *)
Definition crtD1F_L4 (cx : crt_cx) (same nsame back : Z) : list (Z * Z) :=
  [(c_text cx - HEAD, FSH_Fn_writer.enc_size (Z.of_nat (length (c_bs cx))) + HEAD);
   (c_want cx, FSH_Fn_writer.enc_size (Z.of_nat (length (c_bs cx))));
   (same, nsame);
   (back - HEAD, FSH_Fn_writer.dec_size (WriterSpec.b64_enc (c_bs cx)) + HEAD)].
Definition crtD1F_H2 (cx : crt_cx) (back : Z) : list (Z * Z) :=
  [(c_text cx - HEAD, HEAD); (back - HEAD, HEAD)].
(* the shared shape's lists, read in the boundary invariants' own literal forms, one equation per X the lane uses
   (the invariants write the blocks of X inline; these are stated, not left to conversion, which would have to
   re-associate the appends) *)
Lemma crtD1F_eqB_f : forall cx s ns b f nf (D : list (Z * Z)),
  crtD1F_L4 cx s ns b ++ rd_hblocks ([] ++ (f, nf) :: []) ++ D =
  [(c_text cx - HEAD, FSH_Fn_writer.enc_size (Z.of_nat (length (c_bs cx))) + HEAD);
   (c_want cx, FSH_Fn_writer.enc_size (Z.of_nat (length (c_bs cx)))); (s, ns);
   (b - HEAD, FSH_Fn_writer.dec_size (WriterSpec.b64_enc (c_bs cx)) + HEAD); (f - HEAD, nf + HEAD)] ++ D.
Proof. intros. unfold crtD1F_L4, rd_hblocks. cbn [app map fst snd]. reflexivity. Qed.
Lemma crtD1F_eqB_0 : forall cx s ns b (D : list (Z * Z)),
  crtD1F_L4 cx s ns b ++ rd_hblocks ([] ++ []) ++ D =
  [(c_text cx - HEAD, FSH_Fn_writer.enc_size (Z.of_nat (length (c_bs cx))) + HEAD);
   (c_want cx, FSH_Fn_writer.enc_size (Z.of_nat (length (c_bs cx)))); (s, ns);
   (b - HEAD, FSH_Fn_writer.dec_size (WriterSpec.b64_enc (c_bs cx)) + HEAD)] ++ D.
Proof. intros. unfold crtD1F_L4, rd_hblocks. cbn [app map fst snd]. reflexivity. Qed.
Lemma crtD1F_eqB_fg : forall cx s ns b f nf g ng (D : list (Z * Z)),
  crtD1F_L4 cx s ns b ++ rd_hblocks ([(f, nf)] ++ (g, ng) :: []) ++ D =
  [(c_text cx - HEAD, FSH_Fn_writer.enc_size (Z.of_nat (length (c_bs cx))) + HEAD);
   (c_want cx, FSH_Fn_writer.enc_size (Z.of_nat (length (c_bs cx)))); (s, ns);
   (b - HEAD, FSH_Fn_writer.dec_size (WriterSpec.b64_enc (c_bs cx)) + HEAD); (f - HEAD, nf + HEAD);
   (g - HEAD, ng + HEAD)] ++ D.
Proof. intros. unfold crtD1F_L4, rd_hblocks. cbn [app map fst snd]. reflexivity. Qed.
Lemma crtD1F_eqB_f0 : forall cx s ns b f nf (D : list (Z * Z)),
  crtD1F_L4 cx s ns b ++ rd_hblocks ([(f, nf)] ++ []) ++ D =
  [(c_text cx - HEAD, FSH_Fn_writer.enc_size (Z.of_nat (length (c_bs cx))) + HEAD);
   (c_want cx, FSH_Fn_writer.enc_size (Z.of_nat (length (c_bs cx)))); (s, ns);
   (b - HEAD, FSH_Fn_writer.dec_size (WriterSpec.b64_enc (c_bs cx)) + HEAD); (f - HEAD, nf + HEAD)] ++ D.
Proof. intros. unfold crtD1F_L4, rd_hblocks. cbn [app map fst snd]. reflexivity. Qed.
Lemma crtD1F_eqU_f : forall cx b f nf (D : list (Z * Z)),
  crtD1F_H2 cx b ++ rd_heads ([] ++ (f, nf) :: []) ++ D =
  [(c_text cx - HEAD, HEAD); (b - HEAD, HEAD); (f - HEAD, HEAD)] ++ D.
Proof. intros. unfold crtD1F_H2, rd_heads. cbn [app map fst snd]. reflexivity. Qed.
Lemma crtD1F_eqU_0 : forall cx b (D : list (Z * Z)),
  crtD1F_H2 cx b ++ rd_heads ([] ++ []) ++ D = [(c_text cx - HEAD, HEAD); (b - HEAD, HEAD)] ++ D.
Proof. intros. unfold crtD1F_H2, rd_heads. cbn [app map fst snd]. reflexivity. Qed.
Lemma crtD1F_eqU_fg : forall cx b f nf g ng (D : list (Z * Z)),
  crtD1F_H2 cx b ++ rd_heads ([(f, nf)] ++ (g, ng) :: []) ++ D =
  [(c_text cx - HEAD, HEAD); (b - HEAD, HEAD); (f - HEAD, HEAD); (g - HEAD, HEAD)] ++ D.
Proof. intros. unfold crtD1F_H2, rd_heads. cbn [app map fst snd]. reflexivity. Qed.
Lemma crtD1F_eqU_f0 : forall cx b f nf (D : list (Z * Z)),
  crtD1F_H2 cx b ++ rd_heads ([(f, nf)] ++ []) ++ D =
  [(c_text cx - HEAD, HEAD); (b - HEAD, HEAD); (f - HEAD, HEAD)] ++ D.
Proof. intros. unfold crtD1F_H2, rd_heads. cbn [app map fst snd]. reflexivity. Qed.
(* ---- the lane's budget arithmetic, each in a SMALL context: `lia` over a boundary's whole hypothesis set with the
   LIVE_* prefixes unfolded does not return (MEASURED: the kernel check of that leaf ran over 5 min on a build machine,
   bisected with `abstract`), so every budget step is one of these lemmas, with the K / CNT / LIVE prefixes as
   atoms. ---- *)
Lemma crtD1F_live_step : forall cx,
  LIVE_82274 cx = LIVE_822ac cx + (FSH_Fn_writer.dec_size (WriterSpec.b64_enc (c_bs cx)) + HEAD).
Proof. intros cx. unfold LIVE_82274, LIVE_822ac. reflexivity. Qed.
Lemma crtD1F_cnt_step : forall cx, CNT_822ac cx = CNT_82274 cx.
Proof. intros cx. unfold CNT_822ac, CNT_82274. reflexivity. Qed.
Lemma crtD1F_k_a4 : forall cx, K_822a4 cx = K_82274 cx + EV_fuzz_free.
Proof. intros cx. reflexivity. Qed.
Lemma crtD1F_k_ac : forall cx, K_822ac cx = K_822a4 cx + EV_fuzz_free.
Proof. intros cx. unfold K_822ac, K_822a4, K_82274. lia. Qed.
Lemma crtD1F_bb32 : forall (bbS bbS' bb0 n : Z) (cx : crt_cx),
  bbS' + (n + HEAD) = bbS -> bbS <= bb0 + LIVE_82274 cx ->
  n = FSH_Fn_writer.dec_size (WriterSpec.b64_enc (c_bs cx)) -> bbS' <= bb0 + LIVE_822ac cx.
Proof. intros bbS bbS' bb0 n cx H1 H2 ->. rewrite crtD1F_live_step in H2. lia. Qed.
Lemma crtD1F_bb33 : forall (bbS bbS' bb0 n L : Z),
  bbS' + (n + HEAD) = bbS -> bbS <= bb0 + L -> 0 < n -> bbS' <= bb0 + L.
Proof. intros bbS bbS' bb0 n L H1 H2 H3. unfold HEAD in H1. lia. Qed.
Lemma crtD1F_room1 : forall k Kx : Z,
  k <= Kx -> Kx + EV_fuzz_free <= EV_check_round_trip -> k + 1 <= EV_check_round_trip.
Proof. intros k Kx H1 H2. unfold EV_fuzz_free in H2. lia. Qed.
Lemma crtD1F_room2 : forall k Kx : Z,
  k <= Kx -> Kx + EV_fuzz_free + EV_fuzz_free <= EV_check_round_trip -> k + 1 <= EV_check_round_trip.
Proof. intros k Kx H1 H2. unfold EV_fuzz_free in H2. lia. Qed.
Lemma crtD1F_kgoal : forall k Kx : Z, k <= Kx -> k + EV_fuzz_free <= Kx + EV_fuzz_free.
Proof. intros k Kx H. lia. Qed.

(* ---- the boundary atoms the fuzz_free boundaries read: s2 s4 s5 s6 s8 s9 s10 s11. s7 (atom 23) is NOT among
   them: at 0x82274 the call site holds the callee's a0 there, not the boundary atom (a Theorem Labs lane 07:5xZ). ---- *)
Definition crtD1F_atoms : list nat := [18; 20; 21; 22; 24; 25; 26; 27]%nat.
Lemma crtD1F_atoms_range : forall j : nat, In j crtD1F_atoms -> (18 <= j <= 27)%nat.
Proof. intros j Hj. unfold crtD1F_atoms in Hj. cbn [In] in Hj. lia. Qed.
Lemma crtD1F_at18 : In 18%nat crtD1F_atoms.
Proof. unfold crtD1F_atoms. cbn [In]. left. reflexivity. Qed.
Lemma crtD1F_at20 : In 20%nat crtD1F_atoms.
Proof. unfold crtD1F_atoms. cbn [In]. right. left. reflexivity. Qed.
Lemma crtD1F_at21 : In 21%nat crtD1F_atoms.
Proof. unfold crtD1F_atoms. cbn [In]. right. right. left. reflexivity. Qed.
Lemma crtD1F_at22 : In 22%nat crtD1F_atoms.
Proof. unfold crtD1F_atoms. cbn [In]. right. right. right. left. reflexivity. Qed.
Lemma crtD1F_at24 : In 24%nat crtD1F_atoms.
Proof. unfold crtD1F_atoms. cbn [In]. right. right. right. right. left. reflexivity. Qed.
Lemma crtD1F_at25 : In 25%nat crtD1F_atoms.
Proof. unfold crtD1F_atoms. cbn [In]. right. right. right. right. right. left. reflexivity. Qed.
Lemma crtD1F_at26 : In 26%nat crtD1F_atoms.
Proof. unfold crtD1F_atoms. cbn [In]. right. right. right. right. right. right. left. reflexivity. Qed.
Lemma crtD1F_at27 : In 27%nat crtD1F_atoms.
Proof. unfold crtD1F_atoms. cbn [In]. right. right. right. right. right. right. right. left. reflexivity. Qed.

Section d1free. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable SK : YI16.sink_head.
Variable B : asyms.
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.

(* ================= what the three fuzz_free boundaries share =================
   The walk's four fixed blocks (text, want, same, back), the two trees with their blocks, and X: the reader blocks
   the lane's frees are still to take (X = [file; got] at 0x82274 / 0x82298, [file] at 0x822a4, [] at 0x822ac). Each
   crossing removes one pair of X. Which atom holds which pointer, and the budgets, stay with the boundary
   invariants; only `same` and `back` are read here, through E.
   Ddoc and Dback are PARAMETERS, not existentials: a free touches neither tree, and the boundary invariants'
   REMAINING ALLOWANCE (base v20 / a Theorem Labs lane) is stated over those two lists, so the crossing must hand the SAME lists
   back to the next boundary. *)
Definition crtD1_H (cx : crt_cx) (E : env) (ly3 : alayout) (S3 : astate) (U3 : list (Z * Z))
    (W3 : world tfibsegs) (mem : word -> option byte) (X Ddoc Dback : list (Z * Z)) (live cnt : Z) : Prop :=
  exists (same nsame back : Z) (tback : PjTree.jv) (peak : Z),
    ew E 24 = Z_to_bv 64 same /\ ew E 25 = Z_to_bv 64 back /\
    Permutation (ablocks B ly3 S3)
      (ablocks B (c_ly cx) (c_S cx) ++ crtD1F_L4 cx same nsame back ++
       rd_hblocks X ++ rd_hblocks (Ddoc ++ Dback)) /\
    Permutation U3 (c_U cx ++ crtD1F_H2 cx back ++ rd_heads X ++ rd_heads (Ddoc ++ Dback)) /\
    FSupoisonU.fs_heads B ly3 S3 U3 /\
    crtD1_common B cx ly3 S3 W3 mem back Ddoc Dback tback /\
    rd_blocks_ok tfibsegs B ly3 S3 W3 mem X /\
    fs_glob tfibsegs W3 mem live peak cnt SIZE_MAXZ /\
    live = c_live cx + FSH_Fn_writer.enc_size (Z.of_nat (length (c_bs cx))) +
           FSH_Fn_writer.dec_size (WriterSpec.b64_enc (c_bs cx)) + rd_sum X + rd_sum (Ddoc ++ Dback).

(* what a lane boundary owes the crossing, and what it gets back: `na` is the atom holding the freed pointer, INV the
   boundary before the call and INV' the boundary at its return. The continuation is handed the post-call shape with
   the pair removed, the exact byte give-back, and the env agreement on s2 .. s11; nothing else changes. *)
Definition crtD1_free_link (na : nat) (INV INV' : crt_inv) : Prop :=
  forall cx E k ly3 S3 U3 (W3 : world tfibsegs) ms3 md3 mx mdx,
  crt_base B cx -> crt_E cx E -> AR tfibsegs B ly3 S3 W3 mx mdx ->
  INV cx E k ly3 S3 U3 W3 ms3 md3 ->
  exists (p n : Z) (X1 X2 Ddoc Dback : list (Z * Z)) (live cnt : Z),
    ew E na = Z_to_bv 64 p /\ 4096 + HEAD <= p /\ k + 1 <= EV_check_round_trip /\
    crtD1_H cx E ly3 S3 U3 W3 (ms_mem ms3) (X1 ++ (p, n) :: X2) Ddoc Dback live cnt /\
    (forall E' ly' S' U' (W' : world tfibsegs) ms' md',
       (forall j : nat, In j crtD1F_atoms -> ew E' j = ew E j) ->
       crtD1_H cx E' ly' S' U' W' (ms_mem ms') (X1 ++ X2) Ddoc Dback (live - n) cnt ->
       blocks_bytes S' + (n + HEAD) = blocks_bytes S3 ->
       INV' cx E' (k + EV_fuzz_free) ly' S' U' W' ms' md').

(* the call site's s2 .. s11 still denote the boundary atoms. At a site the engine reached with no write to them that
   is crt_ssave; segment 31's empty-body arm re-seats s11 on the frame atom and its INV pins the value. *)
Definition crtD1_sreg (ssC : sstate) (INV : crt_inv) : Prop :=
  forall cx E k ly3 S3 U3 (W3 : world tfibsegs) ms3 md3,
  crt_base B cx -> crt_E cx E -> INV cx E k ly3 S3 U3 W3 ms3 md3 ->
  forall j : nat, In j crtD1F_atoms ->
    sv_denot E (sr_get (ss_regs ssC) (Z_to_bv 5 (Z.of_nat j))) = ew E j.
Lemma crtD1_sreg_of_ssave : forall ssC INV, crt_ssave ssC -> crtD1_sreg ssC INV.
Proof.
intros ssC INV H. intros cx E k ly3 S3 U3 W3 ms3 md3 _ _ _ j Hj.
rewrite (H j (crtD1F_atoms_range j Hj)). apply fsw_SOff0.
Qed.

(* ---- a block of the boundary's list other than the freed one is a DIFFERENT pair: the walk's list has no
   duplicate, which is crtD1_not_entry read on both sides of the freed pair ---- *)
Lemma crtD1F_ne : forall ly3 S3 (W : world tfibsegs) mem md (L1 L2 : list (Z * Z)) x b,
  AR tfibsegs B ly3 S3 W mem md -> Permutation (ablocks B ly3 S3) (L1 ++ x :: L2) ->
  In b (L1 ++ L2) -> b <> x.
Proof.
intros ly3 S3 W mem md L1 L2 x b HAR HP Hin E. subst b. destruct x as [bx nx].
assert (HP2 : Permutation (ablocks B ly3 S3) ((L1 ++ [(bx, nx)]) ++ L2))
  by (rewrite <- crtD1F_cons_app; exact HP).
apply in_app_iff in Hin as [Hin|Hin].
- exact (crtD1_not_entry B ly3 S3 W mem md L1 ((bx, nx) :: L2) bx nx HAR HP (or_introl eq_refl) Hin).
- exact (crtD1_not_entry B ly3 S3 W mem md (L1 ++ [(bx, nx)]) L2 bx nx HAR HP2 Hin
    ltac:(apply in_or_app; right; left; reflexivity)).
Qed.

(* ---- the shared shape reads the same at a memory that agrees below alloc_ceiling (the store-free run to the call
   writes only the s0 words and the s1 slots, both above alloc_ceiling) ---- *)
Lemma crtD1_H_below : forall cx E ly3 S3 U3 (W3 : world tfibsegs) mx mdx m m' X Ddoc Dback live cnt,
  AR tfibsegs B ly3 S3 W3 mx mdx -> same_below m m' alloc_ceiling ->
  crtD1_H cx E ly3 S3 U3 W3 m X Ddoc Dback live cnt -> crtD1_H cx E ly3 S3 U3 W3 m' X Ddoc Dback live cnt.
Proof.
intros cx E ly3 S3 U3 W3 mx mdx m m' X Ddoc Dback live cnt HAR HS
  (same & nsame & back & tback & peak & E24 & E25 & HPB & HPU & HHD & HC & HX & HG & HL).
destruct HC as (HCt & HCb & HCtree & HCnode & HCdep & HCp1 & HCp2).
destruct (fsw_pobj_low B ly3 S3 W3 mx mdx m (crt_F cx + 0x140) HAR HCp1) as (Hv1a & Hv1b).
destruct (fsw_pobj_low B ly3 S3 W3 mx mdx m (crt_F cx + 0x20) HAR HCp2) as (Hv2a & Hv2b).
assert (Ht : fs_rblock tfibsegs B ly3 S3 W3 m' (c_text cx) (FSH_Fn_writer.enc_size (Z.of_nat (length (c_bs cx)))))
  by (eapply fs_rblock_below; [exact HAR | exact HS | exact HCt]).
assert (Hb : fs_rblock tfibsegs B ly3 S3 W3 m' back (FSH_Fn_writer.dec_size (WriterSpec.b64_enc (c_bs cx))))
  by (eapply fs_rblock_below; [exact HAR | exact HS | exact HCb]).
assert (Htree : rtree tfibsegs B ly3 S3 W3 m' (crt_F cx + 0x20)
  (PjTree.JObj (check_round_trip_stages_b.crt_doc (WriterSpec.b64_enc (c_bs cx)))) Ddoc).
{ unfold rtree in HCtree |- *. eapply rnode_below; [exact HAR | exact HS | lia | lia | exact HCtree]. }
assert (Hnode : rnode tfibsegs B ly3 S3 W3 m' (Ddoc ++ Dback) (crt_F cx + 0x140) tback Dback)
  by (eapply rnode_below; [exact HAR | exact HS | lia | lia | exact HCnode]).
assert (Hp1 : pobj tfibsegs B ly3 S3 W3 m' (crt_F cx + 0x140))
  by (eapply pobj_below; [exact HAR | exact HS | exact HCp1]).
assert (Hp2 : pobj tfibsegs B ly3 S3 W3 m' (crt_F cx + 0x20))
  by (eapply pobj_below; [exact HAR | exact HS | exact HCp2]).
exists same, nsame, back, tback, peak.
split; [exact E24|]. split; [exact E25|]. split; [exact HPB|]. split; [exact HPU|]. split; [exact HHD|].
split.
- split; [exact Ht|]. split; [exact Hb|]. split; [exact Htree|]. split; [exact Hnode|].
  split; [exact HCdep|]. split; [exact Hp1 | exact Hp2].
- split; [eapply rd_blocks_ok_below; [exact HAR | exact HS | exact HX]|].
  split; [eapply fs_glob_below; [exact HS | exact HG] | exact HL].
Qed.

(* ================= the lane's fuzz_free crossing, once =================
   From any call-site state ssC whose a0 is the atom `na`, under the link between INV and INV': the callee's fpreU
   (crt_hcall's own premise, from crt_site_pre), fuzz_free_spec on its p <> 0 arm, the footprint
   FS_PSTAT_FP ++ the freed block, and the next boundary from the callee's post. *)
Hypothesis FUZZ_FREE : @fuzz_free_spec fx rc SK tfibsegs B.

Lemma crtD1_free_hcall : forall (ssC : sstate) (r : Z) (na : nat) (INV INV' : crt_inv),
  sr_get (ss_regs ssC) 10%bv = SOff na 0 ->
  crtD1_sreg ssC INV ->
  crtD1_free_link na INV INV' ->
  crt_hcall SK B ssC A_fuzz_free r STK_fuzz_free INV INV'.
Proof.
intros ssC r na INV INV' G10 HSREG HLINK.
intros cx E k ly3 S3 U3 W3 ms3 md3 regsC memC mdC HB HE HINV HJC HARUC Hfr HSB RG HPREc HFRL HTOPc.
pose proof HB as (HBpre & HBheads & HBsp & HBfrl & HB10 & HB11 & HB12 & HBz & HBnz & HBtb & HBwin & HBpt &
  HBdec & HBbd & HBzb & HBrb & HBstat & HBq & HBlive & HBrd & HBsp47 & HBnev & HBbb).
pose proof (ARU_AR tfibsegs B _ _ _ _ _ _ HARUC) as HARC.
destruct (HLINK cx E k ly3 S3 U3 W3 ms3 md3 (unpoison U3 memC) mdC HB HE HARC HINV)
  as (p & n & X1 & X2 & Ddoc & Dback & live & cnt & Ena & Hp4096 & Hroom & HH3 & CONT).
pose proof (crtD1_H_below cx E ly3 S3 U3 W3 _ _ (ms_mem ms3) memC _ Ddoc Dback live cnt HARC HSB HH3) as HH.
destruct HH as (same & nsame & back & tback & peak & E24 & E25 & HPB & HPU & HHD & HC & HX & HG & HL).
pose proof HC as (HCt & HCb & HCtree & HCnode & HCdep & HCp1 & HCp2).
(* the freed pair is (p - HEAD, n + HEAD); it is written out, since the byte count reads its second component *)
set (FPc := FS_PSTAT_FP ++ ablocks_fp [(p - HEAD, n + HEAD)]).
set (A0 := ablocks B (c_ly cx) (c_S cx)) in *.
set (L4 := crtD1F_L4 cx same nsame back) in *.
(* Ddoc ++ Dback is written out: the live equation is read by lia, which compares atoms, not let-bound names *)
(* the big lists, split at the freed pair *)
rewrite (crtD1F_rdh_split X1 X2 p n) in HPB. rewrite crtD1F_split in HPB.
rewrite (crtD1F_rdhd_split X1 X2 p n) in HPU. rewrite crtD1F_split in HPU.
(* the freed block is one of the boundary's blocks and its head one of the boundary's heads *)
assert (HinB : In (p - HEAD, n + HEAD) (ablocks B ly3 S3)).
{ apply (Permutation_in _ (Permutation_sym HPB)). apply in_or_app. right. left. reflexivity. }
assert (HinU : In (p - HEAD, HEAD) U3).
{ apply (Permutation_in _ (Permutation_sym HPU)). apply in_or_app. right. left. reflexivity. }
destruct (in_split _ _ HinU) as (U1 & U2 & EU).
(* the freed block's own data, and the sizes of everything g_live counts *)
assert (HrbP : fs_rblock tfibsegs B ly3 S3 W3 memC p n) by (apply HX; apply in_or_app; right; left; reflexivity).
pose proof HrbP as (_ & _ & Hnpos & _).
assert (HDrbo : rd_blocks_ok tfibsegs B ly3 S3 W3 memC (Ddoc ++ Dback))
  by (destruct HCnode as (_ & Hbk & _); exact Hbk).
assert (HD0 : 0 <= rd_sum (Ddoc ++ Dback)) by (eapply crt_rd_sum_pos; exact HDrbo).
destruct (crt_rbo_app B ly3 S3 W3 memC X1 ((p, n) :: X2) HX) as (HX1 & HX2').
assert (HX2 : rd_blocks_ok tfibsegs B ly3 S3 W3 memC X2) by (intros a kk Hk; apply HX2'; right; exact Hk).
assert (HXr : rd_blocks_ok tfibsegs B ly3 S3 W3 memC (X1 ++ X2)).
{ intros a kk Hin. apply in_app_iff in Hin as [Hin|Hin]; [exact (HX1 a kk Hin) | exact (HX2 a kk Hin)]. }
assert (HX10 : 0 <= rd_sum X1) by (eapply crt_rd_sum_pos; exact HX1).
assert (HX20 : 0 <= rd_sum X2) by (eapply crt_rd_sum_pos; exact HX2).
assert (ErdsX : rd_sum (X1 ++ (p, n) :: X2) = rd_sum X1 + (n + rd_sum X2)).
{ rewrite crt_rd_sum_app. unfold rd_sum at 2. cbn [fold_right snd]. reflexivity. }
pose proof HCt as (_ & _ & Hencpos & _). pose proof HCb as (_ & _ & Hdecpos & _).
assert (Hlive0 : 0 <= c_live cx) by (eapply crt_live0; exact HB).
assert (Hnlive : n <= live) by (rewrite HL, ErdsX; lia).
(* room for one more event *)
pose proof HJC as (HARj & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk0 & _).
assert (Hev : st_nev S3 + 1 <= EV_MAX) by lia.
(* the call's argument register *)
assert (Ra0 : YK11.getr regsC 10 = w64 p) by (rewrite (RG 10%bv), G10, fsw_SOff0, Ena; reflexivity).
(* fuzz_free's contract at this call, on its p <> 0 arm *)
assert (HARM : (p = 0 /\ fpreU tfibsegs B STK_fuzz_free ly3 S3 U3 W3 regsC memC mdC (crt_ch1 cx)) \/
  (p <> 0 /\ exists Ua Ub, U3 = Ua ++ (p - HEAD, HEAD) :: Ub /\
     fpreU tfibsegs B STK_fuzz_free ly3 S3 U3 W3 regsC memC mdC (crt_ch1 cx) /\
     fs_rblock tfibsegs B ly3 S3 W3 memC p n /\ n <= live)).
{ right. split; [unfold HEAD in Hp4096; lia|]. exists U1, U2.
  split; [exact EU|]. split; [exact HPREc|]. split; [exact HrbP | exact Hnlive]. }
unfold fuzz_free_spec in FUZZ_FREE.
specialize (FUZZ_FREE ly3 S3 U3 W3 regsC memC mdC (crt_ch1 cx) p n live peak cnt SIZE_MAXZ
  Ra0 HG HHD HARM ltac:(intros _; exact Hev)).
exists FPc, 1.
eexists. split; [exact FUZZ_FREE|].
(* the footprint: the statics are image bytes; the freed block is a temporary block of the walk *)
assert (HFPsub : fsw_fp_sub B (c_ly cx) (c_S cx) ly3 S3 [(3, c_pos cx)] FS_PSTAT_FP FPc).
{ intros a Ha. apply inFP_app in Ha as [Ha|Ha].
  - right. right. left. split; [exact Ha | exact (crt_pstat_img a Ha)].
  - right. left. apply inFP_ablocks_fp_inv in Ha as (q & m & Hq & Hr).
    destruct Hq as [Eq|[]]. injection Eq as <- <-.
    exists (p - HEAD), (n + HEAD). split; [exact HinB | split; [|exact Hr]].
    intros Hbad.
    exact (crtD1_not_entry B ly3 S3 W3 (unpoison U3 memC) mdC A0
      (L4 ++ (rd_hblocks X1 ++ (p - HEAD, n + HEAD) :: rd_hblocks X2) ++ rd_hblocks (Ddoc ++ Dback))
      (p - HEAD) (n + HEAD) HARC
      ltac:(rewrite crtD1F_split; exact HPB)
      ltac:(apply in_or_app; right; apply in_or_app; left; apply in_or_app; right; left; reflexivity)
      Hbad). }
split; [exact HFPsub|].
(* the separation facts of this footprint *)
assert (HinF3 : In (3, c_pos cx) (frames S3)) by (rewrite Hfr; left; reflexivity).
pose proof (crt_F_ly cx _ ly3 Hly) as EFA.
destruct (crtD1_free_fp_clear B ly3 S3 W3 (unpoison U3 memC) mdC p n HARC HinB)
  as (FPblk & FPfrm & FPsh).
assert (HFPframe : forall a, crt_F cx <= a < crt_F cx + 512 -> ~ inFP FPc a).
{ intros a Ha. apply (FPfrm 3 (c_pos cx) a HinF3). left. rewrite EFA, crt_frame3. lia. }
split.
{ intros a Ha. apply HFPframe. rewrite crt_frame3 in Ha. lia. }
(* every block of the boundary other than the freed one is a different pair, so its bytes and head are off FPc *)
assert (HNE : forall b, In b ((A0 ++ L4 ++ rd_hblocks X1) ++
    (rd_hblocks X2 ++ rd_hblocks (Ddoc ++ Dback))) ->
  b <> (p - HEAD, n + HEAD)).
{ intros b Hb. exact (crtD1F_ne ly3 S3 W3 (unpoison U3 memC) mdC _ _ (p - HEAD, n + HEAD) b HARC HPB Hb). }
assert (HKEEP : forall a kk, In (a - HEAD, kk + HEAD) (ablocks B ly3 S3) ->
  (a - HEAD, kk + HEAD) <> (p - HEAD, n + HEAD) ->
  0 <= kk -> forall y, a - HEAD <= y < a + kk -> ~ inFP FPc y).
{ intros a kk Hin Hne Hk y Hy.
  destruct (req_size_pos (kk + HEAD) ltac:(unfold HEAD; lia)) as (_ & Hrs).
  apply (FPblk (a - HEAD) (kk + HEAD) y Hin Hne). unfold HEAD in *. lia. }
assert (HFt : forall y, c_text cx - HEAD <= y < c_text cx + FSH_Fn_writer.enc_size (Z.of_nat (length (c_bs cx))) ->
  ~ inFP FPc y).
{ apply HKEEP; [exact (proj1 HCt) | | lia].
  apply HNE. apply in_or_app. left. apply in_or_app. right. apply in_or_app. left. left. reflexivity. }
assert (HFb : forall y, back - HEAD <= y < back + FSH_Fn_writer.dec_size (WriterSpec.b64_enc (c_bs cx)) ->
  ~ inFP FPc y).
{ apply HKEEP; [exact (proj1 HCb) | | lia].
  apply HNE. apply in_or_app. left. apply in_or_app. right. apply in_or_app. left.
  right. right. right. left. reflexivity. }
assert (HFD : forall a kk y, In (a, kk) (Ddoc ++ Dback) -> a - HEAD <= y < a + kk -> ~ inFP FPc y).
{ intros a kk y Hin Hy. destruct (HDrbo a kk Hin) as (Hinb & _ & Hkk & _).
  apply (HKEEP a kk Hinb); [|lia|exact Hy].
  apply HNE. apply in_or_app. right. apply in_or_app. right.
  unfold rd_hblocks. apply in_map_iff. exists (a, kk). split; [reflexivity | exact Hin]. }
assert (HFX : forall a kk y, In (a, kk) (X1 ++ X2) -> a - HEAD <= y < a + kk -> ~ inFP FPc y).
{ intros a kk y Hin Hy.
  assert (Hib : In (a - HEAD, kk + HEAD) (ablocks B ly3 S3) /\ 0 < kk).
  { apply in_app_iff in Hin as [Hin|Hin].
    - destruct (HX1 a kk Hin) as (Hbk & _ & Hk & _). split; [exact Hbk | exact Hk].
    - destruct (HX2 a kk Hin) as (Hbk & _ & Hk & _). split; [exact Hbk | exact Hk]. }
  destruct Hib as (Hib & Hkk).
  apply (HKEEP a kk Hib); [|lia|exact Hy].
  apply HNE. apply in_app_iff in Hin as [Hin|Hin].
  - apply in_or_app. left. apply in_or_app. right. apply in_or_app. right.
    unfold rd_hblocks. apply in_map_iff. exists (a, kk). split; [reflexivity | exact Hin].
  - apply in_or_app. right. apply in_or_app. left.
    unfold rd_hblocks. apply in_map_iff. exists (a, kk). split; [reflexivity | exact Hin]. }
assert (HFdoc : forall a kk y, In (a, kk) Ddoc -> a - HEAD <= y < a + kk -> ~ inFP FPc y)
  by (intros a kk y Hin; apply HFD; apply in_or_app; left; exact Hin).
assert (HFv1 : forall y, crt_F cx + 0x140 <= y < crt_F cx + 0x140 + 56 -> ~ inFP FPc y)
  by (intros y Hy; apply HFPframe; lia).
assert (HFv2 : forall y, crt_F cx + 0x20 <= y < crt_F cx + 0x20 + 56 -> ~ inFP FPc y)
  by (intros y Hy; apply HFPframe; lia).
assert (HFPsh : forall a, inFP FPc a -> ~ (SHADOW_OFF <= a < SHADOW_OFF + 2 ^ 44)) by exact FPsh.
(* the callee's post: the block list and U with the freed pair gone, and the data facts transported *)
intros W' c' HP'.
destruct HP' as [(H0 & _) | (_ & U1' & U2' & EU' & HPOST)]; [unfold HEAD in Hp4096; lia|].
destruct HPOST as (ly' & S' & regs' & mem' & md' & Ec' & HJc & OK' & PO' & HPR & HQ).
destruct HQ as ((l1 & l2 & El1 & El2) & HH' & HG').
exists ly', S', (U1' ++ U2'), regs', mem', md'.
split; [exact Ec'|]. split; [exact HJc|]. split; [exact OK'|]. split; [exact PO'|]. split; [exact HPR|].
intros HJ' HARU'.
(* the env at the return: s2 .. s11 are the caller's, through aregs_preserved *)
assert (HEJ : forall j : nat, In j crtD1F_atoms -> ew (Ereg regs' (crt_extra cx)) j = ew E j).
{ intros j Hj. pose proof (crtD1F_atoms_range j Hj) as Hr.
  assert (Hjb : Z.of_nat j = bv_unsigned (Z_to_bv 5 (Z.of_nat j)))
    by (symmetry; apply crtD1F_bv5; lia).
  rewrite (ew_Ereg_nat regs' (crt_extra cx) j (Z_to_bv 5 (Z.of_nat j)) Hjb).
  rewrite (HPR (Z.of_nat j) ltac:(unfold acallee_saved; lia)).
  rewrite <- (HSREG cx E k ly3 S3 U3 W3 ms3 md3 HB HE HINV j Hj). apply RG. }
(* the blocks and the heads with the freed pair peeled off *)
rewrite El1 in HPB. rewrite EU' in HPU.
pose proof (Permutation_app_inv _ _ _ _ _ HPB) as HPBc.
pose proof (Permutation_app_inv _ _ _ _ _ HPU) as HPUc.
rewrite crtD1F_join, <- crtD1F_rdh_app in HPBc.
rewrite crtD1F_join, <- crtD1F_rdhd_app in HPUc.
assert (HPB' : Permutation (ablocks B ly' S')
  (A0 ++ L4 ++ rd_hblocks (X1 ++ X2) ++ rd_hblocks (Ddoc ++ Dback))) by (rewrite El2; exact HPBc).
(* the byte give-back *)
assert (EBB : blocks_bytes S' + (n + HEAD) = blocks_bytes S3).
{ assert (E3 : blocks_bytes S3 = bsum (ablocks B ly3 S3)) by apply blocks_bytes_bsum.
  assert (E4 : blocks_bytes S' = bsum (ablocks B ly' S')) by apply blocks_bytes_bsum.
  rewrite E3, E4, El1, El2, !bsum_app, bsum_cons. cbn [snd]. lia. }
(* the boundary shape at the return *)
assert (HH2 : crtD1_H cx (Ereg regs' (crt_extra cx)) ly' S' (U1' ++ U2') W' mem' (X1 ++ X2) Ddoc Dback
  (live - n) cnt).
{ exists same, nsame, back, tback, peak.
  split; [rewrite (HEJ 24%nat crtD1F_at24); exact E24|].
  split; [rewrite (HEJ 25%nat crtD1F_at25); exact E25|].
  split; [exact HPB'|]. split; [exact HPUc|]. split; [exact HH'|].
  split.
  - split; [eapply (fs_rblock_kept_call (SK:=SK));
      [exact HJc | exact HARUC | exact OK' | exact PO' | exact HFt | exact HCt]|].
    split; [eapply (fs_rblock_kept_call (SK:=SK));
      [exact HJc | exact HARUC | exact OK' | exact PO' | exact HFb | exact HCb]|].
    split; [eapply (rtree_kept_call (SK:=SK));
      [exact HJc | exact HARUC | exact OK' | exact PO' | exact HFv2 | exact HFdoc | exact HCp2 | exact HCtree]|].
    split; [eapply (rnode_kept_call (SK:=SK));
      [exact HJc | exact HARUC | exact OK' | exact PO' | exact HFv1 | exact HFD | exact HCp1 | exact HCnode]|].
    split; [exact HCdep|].
    split; [eapply (pobj_kept_call (SK:=SK));
      [exact HJc | exact HARUC | exact OK' | exact PO' | exact HFv1 | exact HFPsh | exact HH' | exact HCp1]|].
    eapply (pobj_kept_call (SK:=SK));
      [exact HJc | exact HARUC | exact OK' | exact PO' | exact HFv2 | exact HFPsh | exact HH' | exact HCp2].
  - split; [eapply (rd_blocks_ok_kept_call (SK:=SK));
      [exact HJc | exact HARUC | exact OK' | exact PO' | exact HFX | exact HXr]|].
    split; [exact HG'|].
    rewrite HL, ErdsX, !crt_rd_sum_app. lia. }
exact (CONT (Ereg regs' (crt_extra cx)) ly' S' (U1' ++ U2') W'
  (mkst regs' (Z_to_bv 64 r) mem' (seg_rom tfibsegs)) md' HEJ HH2 EBB).
Qed.

(* No room hypothesis: each boundary's REMAINING ALLOWANCE gives `k + 1 <= EV_check_round_trip` outright, since
   EV_pj_free of a block list is not negative and CRT_EV_WRAP is positive. *)
Lemma crtD1F_pjfree_pos : forall D : list (Z * Z), 0 <= EV_pj_free D.
Proof. intros D. unfold EV_pj_free, EV_fuzz_free. lia. Qed.
Lemma crtD1F_room_alw2 : forall k a b : Z, 0 <= a -> 0 <= b ->
  k + 2 * EV_fuzz_free + a + b + 2 * EV_fuzz_free + 2 * CRT_EV_WRAP <= EV_check_round_trip ->
  k + 1 <= EV_check_round_trip.
Proof. intros k a b Ha Hb H. unfold EV_fuzz_free, CRT_EV_WRAP in H. lia. Qed.
Lemma crtD1F_room_alw1 : forall k a b : Z, 0 <= a -> 0 <= b ->
  k + EV_fuzz_free + a + b + 2 * EV_fuzz_free + 2 * CRT_EV_WRAP <= EV_check_round_trip ->
  k + 1 <= EV_check_round_trip.
Proof. intros k a b Ha Hb H. unfold EV_fuzz_free, CRT_EV_WRAP in H. lia. Qed.
Lemma crtD1F_alw32 : forall k a b : Z,
  k + 2 * EV_fuzz_free + a + b + 2 * EV_fuzz_free + 2 * CRT_EV_WRAP <= EV_check_round_trip ->
  k + EV_fuzz_free + EV_fuzz_free + a + b + 2 * EV_fuzz_free + 2 * CRT_EV_WRAP <= EV_check_round_trip.
Proof. intros k a b H. lia. Qed.
Lemma crtD1F_alw33 : forall k a b : Z,
  k + EV_fuzz_free + a + b + 2 * EV_fuzz_free + 2 * CRT_EV_WRAP <= EV_check_round_trip ->
  k + EV_fuzz_free + a + b + 2 * EV_fuzz_free + 2 * CRT_EV_WRAP <= EV_check_round_trip.
Proof. intros k a b H. exact H. Qed.

(* ================= segment 33: fuzz_free (file), 0x822a4 -> 0x822ac =================
   The lane's LAST call: X = [(file, nfile)] becomes [], U gives up file's head and g_live drops by nfile, which is
   crt_INV_822ac. The byte bound is the tight one of crtD1_INV_822a4 (LIVE_822ac, a Theorem Labs lane 05:4xZ): this free only gives
   bytes back, so the prefix bound carries over. *)
Lemma crtD1_link33 : crtD1_free_link 22 (crtD1_INV_822a4 B) (crt_INV_822ac B).
Proof.
intros cx E k ly3 S3 U3 W3 ms3 md3 mx mdx HB HE HAR HINV.
destruct HINV as (E18 & E20 & E21 & E26 & E27 &
  (same & nsame & file & nfile & back & Dback & Ddoc & tback & live & peak & cnt &
   E22 & E24 & E25 & HPB & HPU & HHD & HC & HRf & HG & HLive & HBB & HCNT & HK & HALW)).
pose proof HRf as (_ & _ & Hnf & _).
exists file, nfile, [], [], Ddoc, Dback, live, cnt.
split; [exact E22|].
split; [exact (proj1 (fsw_rblock_low B ly3 S3 W3 mx mdx (ms_mem ms3) file nfile HAR HRf))|].
split; [exact (crtD1F_room_alw1 k _ _ (crtD1F_pjfree_pos Dback) (crtD1F_pjfree_pos Ddoc) HALW)|].
split.
- exists same, nsame, back, tback, peak.
  split; [exact E24|]. split; [exact E25|].
  split; [rewrite crtD1F_eqB_f; exact HPB|]. split; [rewrite crtD1F_eqU_f; exact HPU|]. split; [exact HHD|].
  split; [exact HC|].
  split; [intros a kk Hin; cbn [app In] in Hin; destruct Hin as [Eq|[]];
          injection Eq as <- <-; exact HRf|].
  split; [exact HG|].
  cbn [app]. rewrite (crtD1F_rds1 file nfile). lia.
- intros E' ly' S' U' W' ms' md' HEJ HH2 EBB.
  destruct HH2 as (same2 & nsame2 & back2 & tback2 & peak2 &
    E24' & E25' & HPB2 & HPU2 & HHD2 & HC2 & _ & HG2 & HL2).
  destruct HC2 as (HCt2 & HCb2 & HCtree2 & HCnode2 & HCdep2 & HCp12 & HCp22).
  split; [rewrite (HEJ 18%nat crtD1F_at18); exact E18|].
  split; [rewrite (HEJ 20%nat crtD1F_at20); exact E20|].
  split; [rewrite (HEJ 21%nat crtD1F_at21); exact E21|].
  split; [rewrite (HEJ 26%nat crtD1F_at26); exact E26|].
  split; [rewrite (HEJ 27%nat crtD1F_at27); exact E27|].
  exists same2, nsame2, back2, Dback, Ddoc, tback2, (live - nfile), peak2, cnt.
  split; [exact E24'|]. split; [exact E25'|].
  split; [rewrite crtD1F_eqB_0 in HPB2; exact HPB2|]. split; [rewrite crtD1F_eqU_0 in HPU2; exact HPU2|].
  split; [exact HHD2|].
  split; [exact HCt2|]. split; [exact HCb2|]. split; [exact HCtree2|].
  split; [exact HCnode2|]. split; [exact HCdep2|].
  split; [exact HCp12|]. split; [exact HCp22|].
  split; [exact HG2|].
  split; [cbn [app] in HL2; rewrite crtD1F_rds0 in HL2; lia|].
  split; [exact (crtD1F_bb33 (blocks_bytes S3) (blocks_bytes S') (blocks_bytes (c_S cx)) nfile
            (LIVE_822ac cx) EBB HBB Hnf)|].
  split; [exact HCNT|].
  split; [rewrite crtD1F_k_ac; exact (crtD1F_kgoal k (K_822a4 cx) HK)|].
  exact (crtD1F_alw33 k (EV_pj_free Dback) (EV_pj_free Ddoc) HALW).
Qed.

Lemma crtD1_seg33 :
  crt_from SK B (crt_ss_ret 0x822ac crt_cs1 crt_csF) (crt_INV_822ac B) ->
  crt_from SK B (crt_ss_ret 0x822a4 crt_cs1 crt_csF) (crtD1_INV_822a4 B).
Proof.
intros NEXT.
destruct crtD1F_stk as (HS1 & HS2).
destruct (crtD1F_r_ok 0x822ac (or_intror eq_refl)) as (Hr1 & Hr2).
eapply (crt_seg_call SK B 0x822a4 A_fuzz_free 0x822ac crtD1F_sc33 (crtD1_INV_822a4 B)
  (crt_INV_822ac B) STK_fuzz_free crtD1F_run33 crtD1F_site33 Hr1 Hr2 HS1 HS2); [|exact NEXT].
apply (crtD1_free_hcall crtD1F_sc33 0x822ac 22 (crtD1_INV_822a4 B) (crt_INV_822ac B) crtD1F_a0_33
  (crtD1_sreg_of_ssave crtD1F_sc33 (crtD1_INV_822a4 B) crtD1F_ssave33) crtD1_link33).
Qed.

(* ================= segment 32: fuzz_free (got), 0x82298 -> 0x822a4 =================
   The `bnez a0` of the bcmp answer is not taken (crtD1_INV_82298's a0 = 0); then X = [(file, nfile); (got, dec)]
   becomes [(file, nfile)]: got's block and head are gone and g_live drops by dec_size tb2, so the prefix byte bound
   tightens from LIVE_82274 to LIVE_822ac = LIVE_82268 exactly. *)
Lemma crtD1_link32 : crtD1_free_link 23 (crtD1_INV_82298 B) (crtD1_INV_822a4 B).
Proof.
intros cx E k ly3 S3 U3 W3 ms3 md3 mx mdx HB HE HAR HINV.
destruct HINV as (E10 & E18 & E20 & E21 & E26 & E27 &
  (same & nsame & file & nfile & back & got & Dback & Ddoc & tback & live & peak & cnt &
   E22 & E24 & E25 & E23 & Hgot & HPB & HPU & HHD & HC & HRf & HRg & HG & HLive & HBB & HCNT & HK & HALW)).
pose proof HRf as (_ & _ & Hnf & _). pose proof HRg as (_ & _ & Hng & _).
exists got, (FSH_Fn_writer.dec_size (WriterSpec.b64_enc (c_bs cx))), [(file, nfile)], [], Ddoc, Dback, live, cnt.
split; [exact E23|].
split; [exact Hgot|].
split; [exact (crtD1F_room_alw2 k _ _ (crtD1F_pjfree_pos Dback) (crtD1F_pjfree_pos Ddoc) HALW)|].
split.
- exists same, nsame, back, tback, peak.
  split; [exact E24|]. split; [exact E25|].
  split; [rewrite crtD1F_eqB_fg; exact HPB|]. split; [rewrite crtD1F_eqU_fg; exact HPU|]. split; [exact HHD|].
  split; [exact HC|].
  split; [intros a kk Hin; cbn [app In] in Hin; destruct Hin as [Eq|[Eq|[]]];
          injection Eq as <- <-; [exact HRf | exact HRg]|].
  split; [exact HG|].
  cbn [app]. rewrite (crtD1F_rds2 file nfile got (FSH_Fn_writer.dec_size (WriterSpec.b64_enc (c_bs cx)))). lia.
- intros E' ly' S' U' W' ms' md' HEJ HH2 EBB.
  destruct HH2 as (same2 & nsame2 & back2 & tback2 & peak2 &
    E24' & E25' & HPB2 & HPU2 & HHD2 & HC2 & HXr2 & HG2 & HL2).
  split; [rewrite (HEJ 18%nat crtD1F_at18); exact E18|].
  split; [rewrite (HEJ 20%nat crtD1F_at20); exact E20|].
  split; [rewrite (HEJ 21%nat crtD1F_at21); exact E21|].
  split; [rewrite (HEJ 26%nat crtD1F_at26); exact E26|].
  split; [rewrite (HEJ 27%nat crtD1F_at27); exact E27|].
  exists same2, nsame2, file, nfile, back2, Dback, Ddoc, tback2,
    (live - FSH_Fn_writer.dec_size (WriterSpec.b64_enc (c_bs cx))), peak2, cnt.
  split; [rewrite (HEJ 22%nat crtD1F_at22); exact E22|].
  split; [exact E24'|]. split; [exact E25'|].
  split; [rewrite crtD1F_eqB_f0 in HPB2; exact HPB2|]. split; [rewrite crtD1F_eqU_f0 in HPU2; exact HPU2|].
  split; [exact HHD2|].
  split; [exact HC2|].
  split; [apply HXr2; left; reflexivity|].
  split; [exact HG2|].
  split; [cbn [app] in HL2; rewrite (crtD1F_rds1 file nfile) in HL2; lia|].
  split; [exact (crtD1F_bb32 (blocks_bytes S3) (blocks_bytes S') (blocks_bytes (c_S cx))
            (FSH_Fn_writer.dec_size (WriterSpec.b64_enc (c_bs cx))) cx EBB HBB eq_refl)|].
  split; [rewrite crtD1F_cnt_step; exact HCNT|].
  split; [rewrite crtD1F_k_a4; exact (crtD1F_kgoal k (K_82274 cx) HK)|].
  exact (crtD1F_alw32 k (EV_pj_free Dback) (EV_pj_free Ddoc) HALW).
Qed.

Lemma crtD1_seg32 :
  crt_from SK B (crt_ss_ret 0x822a4 crt_cs1 crt_csF) (crtD1_INV_822a4 B) ->
  crt_from SK B (crt_ss_ret 0x82298 crt_cs1 crt_csF) (crtD1_INV_82298 B).
Proof.
intros NEXT.
destruct crtD1F_stk as (HS1 & HS2).
destruct (crtD1F_r_ok 0x822a4 (or_introl eq_refl)) as (Hr1 & Hr2).
eapply (crt_seg_call_br SK B 0x82298 A_fuzz_free 0x822a4 crtD1F_sb32 crtD1F_sc32 (crtD1_INV_82298 B)
  (crtD1_INV_822a4 B) STK_fuzz_free crtD1F_br32 crtD1F_run32 crtD1F_site32 Hr1 Hr2 HS1 HS2
  ltac:(intros cx E k ly3 S3 U3 W3 ms3 md3 HINV; exact (proj1 HINV))); [|exact NEXT].
apply (crtD1_free_hcall crtD1F_sc32 0x822a4 23 (crtD1_INV_82298 B) (crtD1_INV_822a4 B) crtD1F_a0_32
  (crtD1_sreg_of_ssave crtD1F_sc32 (crtD1_INV_82298 B) crtD1F_ssave32) crtD1_link32).
Qed.

(* ================= the empty-body arm of segment 31: fuzz_free (got) straight from 0x82274 =================
   When |bs| = 0 the `beqz s4` at 0x82284 skips the bcmp, so the SAME call of fuzz_free (got) is reached from
   0x82274 with got at atom 10 and the boundary crtD1_INV_82274 (a Theorem Labs lane's FREEZ). The holdings are 0x82298's
   with got read off atom 10 instead of atom 23, so the link is the same instance of crtD1_free_link; the call-site
   state crtD1_sc31z has s11 re-seated on the frame atom (SOff 47 0x1a0), whose value the invariant pins. ---- *)
Lemma crtD1F_sreg31z : crtD1_sreg crtD1_sc31z
  (fun cx E k ly3 S3 U3 W3 ms3 md3 =>
     crtD1_INV_82274 B cx E k ly3 S3 U3 W3 ms3 md3 /\ Z.of_nat (length (c_bs cx)) = 0).
Proof.
intros cx E k ly3 S3 U3 W3 ms3 md3 HB HE (HINV & _) j Hj.
destruct (Nat.eq_dec j 27) as [->|Hne].
- assert (G : sr_get (ss_regs crtD1_sc31z) (Z_to_bv 5 (Z.of_nat 27)) = SOff 47 0x1a0)
    by (vm_compute; reflexivity).
  rewrite G. cbn [sv_denot]. rewrite (crt_E_F cx E HE), Z_to_bv_unsigned_add.
  pose proof HINV as (_ & _ & _ & _ & E27 & _). symmetry. exact E27.
- assert (HD : forallb (fun n => sv_eqb (sr_get (ss_regs crtD1_sc31z) (Z_to_bv 5 (Z.of_nat n))) (SOff n 0))
    [18; 20; 21; 22; 24; 25; 26]%nat = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in HD.
  assert (Hj' : In j [18; 20; 21; 22; 24; 25; 26]%nat).
  { unfold crtD1F_atoms in Hj. cbn [In] in Hj |- *.
    destruct Hj as [Hx|[Hx|[Hx|[Hx|[Hx|[Hx|[Hx|[Hx|[]]]]]]]]]; subst j;
      [ left; reflexivity | right; left; reflexivity | right; right; left; reflexivity
      | right; right; right; left; reflexivity
      | right; right; right; right; left; reflexivity
      | right; right; right; right; right; left; reflexivity
      | right; right; right; right; right; right; left; reflexivity
      | exfalso; exact (Hne eq_refl) ]. }
  assert (G : sr_get (ss_regs crtD1_sc31z) (Z_to_bv 5 (Z.of_nat j)) = SOff j 0)
    by (apply sv_eqb_eq; exact (HD j Hj')).
  rewrite G. apply fsw_SOff0.
Qed.

Lemma crtD1_linkz : crtD1_free_link 10
  (fun cx E k ly3 S3 U3 W3 ms3 md3 =>
     crtD1_INV_82274 B cx E k ly3 S3 U3 W3 ms3 md3 /\ Z.of_nat (length (c_bs cx)) = 0)
  (crtD1_INV_822a4 B).
Proof.
intros cx E k ly3 S3 U3 W3 ms3 md3 mx mdx HB HE HAR HINV.
destruct HINV as ((E18 & E20 & E21 & E26 & E27 &
  (same & nsame & file & nfile & back & got & Dback & Ddoc & tback & live & peak & cnt &
   E22 & E24 & E25 & E10 & Hgot & HPB & HPU & HHD & HC & HRf & HRg & Hzb & Hval & Hra & HG & HLive & HBB &
   HCNT & HK & HALW)) & Hlen).
pose proof HRf as (_ & _ & Hnf & _). pose proof HRg as (_ & _ & Hng & _).
exists got, (FSH_Fn_writer.dec_size (WriterSpec.b64_enc (c_bs cx))), [(file, nfile)], [], Ddoc, Dback, live, cnt.
split; [exact E10|].
split; [exact Hgot|].
split; [exact (crtD1F_room_alw2 k _ _ (crtD1F_pjfree_pos Dback) (crtD1F_pjfree_pos Ddoc) HALW)|].
split.
- exists same, nsame, back, tback, peak.
  split; [exact E24|]. split; [exact E25|].
  split; [rewrite crtD1F_eqB_fg; exact HPB|]. split; [rewrite crtD1F_eqU_fg; exact HPU|]. split; [exact HHD|].
  split; [exact HC|].
  split; [intros a kk Hin; cbn [app In] in Hin; destruct Hin as [Eq|[Eq|[]]];
          injection Eq as <- <-; [exact HRf | exact HRg]|].
  split; [exact HG|].
  cbn [app]. rewrite (crtD1F_rds2 file nfile got (FSH_Fn_writer.dec_size (WriterSpec.b64_enc (c_bs cx)))). lia.
- intros E' ly' S' U' W' ms' md' HEJ HH2 EBB.
  destruct HH2 as (same2 & nsame2 & back2 & tback2 & peak2 &
    E24' & E25' & HPB2 & HPU2 & HHD2 & HC2 & HXr2 & HG2 & HL2).
  split; [rewrite (HEJ 18%nat crtD1F_at18); exact E18|].
  split; [rewrite (HEJ 20%nat crtD1F_at20); exact E20|].
  split; [rewrite (HEJ 21%nat crtD1F_at21); exact E21|].
  split; [rewrite (HEJ 26%nat crtD1F_at26); exact E26|].
  split; [rewrite (HEJ 27%nat crtD1F_at27); exact E27|].
  exists same2, nsame2, file, nfile, back2, Dback, Ddoc, tback2,
    (live - FSH_Fn_writer.dec_size (WriterSpec.b64_enc (c_bs cx))), peak2, cnt.
  split; [rewrite (HEJ 22%nat crtD1F_at22); exact E22|].
  split; [exact E24'|]. split; [exact E25'|].
  split; [rewrite crtD1F_eqB_f0 in HPB2; exact HPB2|]. split; [rewrite crtD1F_eqU_f0 in HPU2; exact HPU2|].
  split; [exact HHD2|].
  split; [exact HC2|].
  split; [apply HXr2; left; reflexivity|].
  split; [exact HG2|].
  split; [cbn [app] in HL2; rewrite (crtD1F_rds1 file nfile) in HL2; lia|].
  split; [exact (crtD1F_bb32 (blocks_bytes S3) (blocks_bytes S') (blocks_bytes (c_S cx))
            (FSH_Fn_writer.dec_size (WriterSpec.b64_enc (c_bs cx))) cx EBB HBB eq_refl)|].
  split; [rewrite crtD1F_cnt_step; exact HCNT|].
  split; [rewrite crtD1F_k_a4; exact (crtD1F_kgoal k (K_82274 cx) HK)|].
  exact (crtD1F_alw32 k (EV_pj_free Dback) (EV_pj_free Ddoc) HALW).
Qed.

Lemma crtD1_freez : crt_hcall SK B crtD1_sc31z A_fuzz_free 0x822a4 STK_fuzz_free
  (fun cx E k ly3 S3 U3 W3 ms3 md3 =>
     crtD1_INV_82274 B cx E k ly3 S3 U3 W3 ms3 md3 /\ Z.of_nat (length (c_bs cx)) = 0)
  (crtD1_INV_822a4 B).
Proof.
apply (crtD1_free_hcall crtD1_sc31z 0x822a4 10 _ (crtD1_INV_822a4 B)
  ltac:(vm_compute; reflexivity) crtD1F_sreg31z crtD1_linkz).
Qed.
End d1free.

Print Assumptions crtD1_free_hcall.
Print Assumptions crtD1_seg32.
Print Assumptions crtD1_seg33.
Print Assumptions crtD1_freez.
