(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr SysStep RzBridge MState.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import Spec ShapeAlg PropExec RelSpec.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CallLit CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Hull Restrict EvtAcct Lazyiq4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIface LayoutPA AClient ATac AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcp0e6.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc AIcp7wm.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpkua.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpkua AIcpnnp AIcpya4 AIcp3q7.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpwpz.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpwpz AIcpw0i.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpq85.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpq85.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcptdg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcptdg AIcp1qh.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIface OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AClient OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc.AIcpdmn OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcp0e6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc.AIcpxbj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc.AIcp6d9 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcp7wm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpkua.AIcpilj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpkua OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpnnp OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpya4 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcp3q7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpwpz.AIcpdm8 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpwpz OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpw0i OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpq85.AIcpa3z OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpq85 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcptdg.AIcp8qs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcptdg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcp1qh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import ExN.   (* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require Import A_World A_Img.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd Require DA_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Exec.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd Require DA_Eg3i DA_Cells DA_Ldix DA_Se7o DA_Tcfe DA_Fh3h DA_S5p6.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd.DA_Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Exec.DA_Myrk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd.DA_Eg3i OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd.DA_Cells OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd.DA_Ldix OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd.DA_Se7o OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd.DA_Tcfe OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd.DA_Fh3h OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd.DA_S5p6.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require RA_seql.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require RA_sjs3.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require RA_sjs3 PF_low PF_file PF_pc1 PF_pc2d PF_vf PF_fpsh PF_vfu PF_pc2s PF_pc2u.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf.RA_seql OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf.RA_sjs3.RA_pdfk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf.RA_sjs3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf.PF_low OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf.PF_file OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf.PF_pc1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf.PF_pc2d OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf.PF_vf OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf.PF_fpsh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf.PF_vfu OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf.PF_pc2s OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf.PF_pc2u.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.
(* [comment removed for export] *)
Ltac mf_easm :=
  lazymatch goal with
  | |- context [mf_set_w _ _ _ _] => cbn_mfp; first [ reflexivity | eassumption ]
  | |- context [mf_set_mode _ _] => cbn_mfp; first [ reflexivity | eassumption ]
  | |- _ => eassumption
  end.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
(* [comment removed for export] *)
From Ltac2 Require Ltac2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require KDrop.
Ltac hot_kdrop := ltac2:(Ltac2.Control.enter (fun () => OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.kdrop_marked ())).
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= hot_kdrop; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_zlit_lazy t ::=
  lazymatch t with
  | context [Z.to_nat _] => fail "symbolic size"
  | _ => let v := eval lazy in t in lazymatch v with Z0 => v | Zpos _ => v | Zneg _ => v end
  end.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaLt.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaLt.lia_tuned.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Ltac2 Require Ltac2.
Ltac2 hot_lia_keep_existing names :=
  let hs := Ltac2.List.map (fun h => let (id, _, _) := h in id) (Ltac2.Control.hyps ()) in
  Ltac2.Std.keep (Ltac2.List.filter (fun n => Ltac2.List.exist (fun h => Ltac2.Ident.equal h n) hs) names).
Ltac hot_lia_cut := ltac2:(Ltac2.Control.enter (fun () => hot_lia_keep_existing [@JBL; @PAB; @SPR; @LO; @CV; @H2; @H; @SPHI; @SZ1; @SZ2; @Ha; @SZ3; @G10; @G11; @RM; @SPP; @H3; @AD2; @CQ; @CEIL; @FIT1; @FIT2; @SL15; @RM0; @S1; @H0; @AD1; @SL16; @R5; @H1; @PAHI; @HK; @ACV; @R2; @ULEN; @S2; @S3; @CM; @H7; @H8; @Hn; @N17; @N0; @FL1; @S0; @Hi; @L; @PALO; @FL2; @R6])).
Ltac hot_lia_full := OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaLt.lia_tuned.
Local Ltac lia ::= hot_lia_cut; hot_lia_full.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma is_prefix_app_mono' {X} : forall (l a b : list X), is_prefix a b -> is_prefix (l ++ a) (l ++ b).
Proof. induction l as [|x l IH]; intros a b H; [exact H|]. cbn. split; [reflexivity| apply IH; exact H]. Qed.

Lemma t_emit_app : forall (a b : list event) (T : TSet), t_eq (t_emit (a ++ b) T) (t_emit a (t_emit b T)).
Proof.
  intros a b T tr. unfold t_emit. split.
  - intros [Hp | (tr' & -> & HT)].
    + apply is_prefix_app_split in Hp as [Hp | (b' & -> & Hp)].
      * left. exact Hp.
      * right. exists b'. split; [reflexivity | left; exact Hp].
    + right. exists (b ++ tr'). split; [rewrite app_assoc; reflexivity|]. right. exists tr'. auto.
  - intros [Hp | (tr' & -> & [Hp | (tr'' & -> & HT)])].
    + left. apply is_prefix_app_r. exact Hp.
    + left. apply is_prefix_app_mono'. exact Hp.
    + right. exists tr''. rewrite app_assoc. auto.
Qed.
Lemma W_app : forall ch (a b : list byte), W ch (a ++ b) = W ch a ++ W ch b.
Proof. intros. unfold W. apply map_app. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma le4_mod32 : forall z, le4 (Z_to_bv 64 (z mod 2^32)) = le4 (Z_to_bv 64 z).
Proof.
  intros z. unfold le4. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64)%Z.
  rewrite !(Z_to_le_bytes_mod 4 _ 64) by (cbn; lia). rewrite (Z_to_le_bytes_mod 4 z 32) by (cbn; lia). reflexivity.
Qed.

Lemma file_at_mode_norm : forall v Fa f mo,
  file_at v Fa (mf_set_mode f mo) -> file_at v Fa (mf_set_mode f (mo mod 2^32)).
Proof.
  intros v Fa f mo H. unfold file_at in *. eapply rw_cells_recast_pf; [exact H| |].
  - destruct H as [[W _] _]. exact W.
  - unfold file_cells. cbn [cells_bytes cbytes mf_set_mode mf_flags mf_rpos mf_rend mf_close mf_wend mf_wpos mf_mbz1 mf_wbase mf_read mf_write mf_seek
      mf_buf mf_bufsize mf_prev mf_next mf_fd mf_pipepid mf_lockcount mf_mode mf_lock mf_lbf mf_pad148].
    rewrite le4_mod32. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ZIMG : Z := 0x7fffa000.   Definition ZIMG_K : nat := 8926.  (* [comment removed for export] *)

Lemma ZIMG_K_val : Z.of_nat ZIMG_K = 8926%Z.
Proof. vm_compute. reflexivity. Qed.

Section CEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Lemma range_ok_of_zeros_low : forall (m : word -> option byte) a n,
  bytes_at rsegs m ZIMG (zeros ZIMG_K) -> 0x10040 <= a -> a + n + 0x80 <= 0x216f0 -> 1 <= n -> range_ok m a n.
Proof.
  intros m a n ZS H1 H2 H3. pose proof ZIMG_K_val as HK. unfold ZIMG in *.
  assert (S1 : 0x7fffa008 <= sha a) by (unfold sha, shadow_off; mlia).
  assert (S2 : sha (a + n - 1) + 16 <= 0x7fffa000 + 8926) by (unfold sha, shadow_off; mlia).
  assert (S3 : sha a <= sha (a + n - 1)) by (unfold sha, shadow_off; mlia).
  split. { left. lia. }
  split.
  { exists (Z.to_nat ((a + n - 1) / 8 - a / 8)), 0. split; [mlia|]. split; [|left; reflexivity].
    replace (zeros (Z.to_nat ((a + n - 1) / 8 - a / 8)) ++ [Z_to_bv 8 0])
      with (zeros (Z.to_nat ((a + n - 1) / 8 - a / 8) + 1)) by (rewrite zeros_app; reflexivity).
    replace (a / 8 + shadow_off) with (0x7fffa000 + (sha a - 0x7fffa000)) by (unfold sha; lia).
    apply (zeros_sub m 0x7fffa000 ZIMG_K); [exact ZS| lia| rewrite HK; unfold sha, shadow_off in *; mlia]. }
  split.
  - replace (sha a - sha a mod 8) with (0x7fffa000 + (sha a - sha a mod 8 - 0x7fffa000)) by lia.
    apply zeros8_mapped8; [| unfold sha, shadow_off in *; mlia].
    apply (zeros_sub m 0x7fffa000 ZIMG_K); [exact ZS| mlia| rewrite HK].
    change (Z.of_nat 8) with 8%Z. pose proof (Z.mod_pos_bound (sha a) 8). lia.
  - replace (sha (a + n - 1) - sha (a + n - 1) mod 8) with (0x7fffa000 + (sha (a + n - 1) - sha (a + n - 1) mod 8 - 0x7fffa000)) by lia.
    apply zeros8_mapped8; [| unfold sha, shadow_off in *; mlia].
    apply (zeros_sub m 0x7fffa000 ZIMG_K); [exact ZS| mlia| rewrite HK].
    change (Z.of_nat 8) with 8%Z. pose proof (Z.mod_pos_bound (sha (a + n - 1)) 8). lia.
Qed.

End CEIL.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Cells.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Variable v : word -> option byte.
  Hypothesis CH : consts_hold LPA v.

  #[using="CH"] Lemma zimg_of_consts : bytes_at rsegs v ZIMG (zeros ZIMG_K).
  Proof. apply (consts_lookup v _ _ CH). vm_compute. reflexivity. Qed.

  #[using="CH"] Lemma fpicpt_cells_of_consts : fpicpt_cells v.
  Proof.
    split; [apply asan_inited_cell_of_bytes; apply (consts_lookup v _ _ CH); vm_compute; reflexivity|].
    split; [apply ro_C8_of_bytes; apply (consts_lookup v _ _ CH); vm_compute; reflexivity|].
    split. { replace 0x146f3c with (0x146ee8 + Z.of_nat 84)%Z by reflexivity.
             eapply (ro_C1_of_nth v 0x146ee8 pa_common_flags_bytes 84); [apply (consts_lookup v _ _ CH); vm_compute; reflexivity| reflexivity]. }
    split; [apply ro_C8_of_bytes; apply (consts_lookup v _ _ CH); vm_compute; reflexivity|].
    exact (map_cells_of_consts v CH).
  Qed.

  #[using="CH"] Lemma strnlen_icpt_cells_of_consts : strnlen_icpt_cells v.
  Proof.
    split; [apply asan_inited_cell_of_bytes; apply (consts_lookup v _ _ CH); vm_compute; reflexivity|].
    split; [apply ro_C8_of_bytes; apply (consts_lookup v _ _ CH); vm_compute; reflexivity|].
    split; [apply ro_C8_of_bytes; apply (consts_lookup v _ _ CH); vm_compute; reflexivity|].
    split. { replace 0x146fe3 with (0x146ee8 + Z.of_nat 251)%Z by reflexivity.
             eapply (ro_C1_of_nth v 0x146ee8 pa_common_flags_bytes 251); [apply (consts_lookup v _ _ CH); vm_compute; reflexivity| reflexivity]. }
    split; [apply ro_C8_of_bytes; apply (consts_lookup v _ _ CH); vm_compute; reflexivity|].
    exact (map_cells_of_consts v CH).
  Qed.

  (* [comment removed for export] *)
  #[using="CH"] Lemma fmt_range_of_consts : forall d, range_ok v (diag_fmt_addr d) (Z.of_nat (cells_size (match d with DF_refused => FMT_REFUSED | _ => s3_fmt d end))).
  Proof. intros []; (apply (range_ok_of_zeros_low v); [exact zimg_of_consts| cbn; lia| cbn; lia| cbn; lia]). Qed.
End Cells.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CEIL2.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Definition s3_fb (d : diag_fmt) : list byte :=
  match d with DF_cannot_open => FMTB_COPEN | DF_read_error => FMTB_RERR | _ => FMTB_USAGE end.
Lemma s3_fb_bytes : forall d, s3_ok d -> cells_bytes (s3_fmt d) = s3_fb d ++ [Z_to_bv 8 0].
Proof. intros [] H; try destruct H; reflexivity. Qed.
Lemma s3_fb_len : forall d, s3_ok d -> Z.of_nat (length (s3_fb d)) + 1 = s3_la d.
Proof. intros [] H; try destruct H; reflexivity. Qed.
Lemma s3_pcm : forall d, s3_ok d -> pcm_stmt_str (s3_fb d).
Proof. intros [] H; try destruct H; [exact pcm_fmt_usage| exact pcm_fmt_copen| exact pcm_fmt_rerr]. Qed.
Lemma s3_pc1 : forall d, s3_ok d -> pass1_stmt (s3_fmt d) (s3_la d).
Proof. intros [] H; try destruct H; [exact pc1_usage| exact pc1_copen| exact pc1_rerr]. Qed.
Lemma s3_addr : forall d, s3_ok d -> 0x10040 <= diag_fmt_addr d /\ diag_fmt_addr d + s3_la d + 0x80 <= 0x216f0.
Proof. intros [] H; try destruct H; cbn; lia. Qed.
Lemma s3_sizes : forall d, s3_ok d ->
  1 <= Z.of_nat (length (s3_L1 d)) <= 19 /\ 1 <= Z.of_nat (length (s3_L2 d)) <= 7
  /\ Z.of_nat (length (s3_L1 d)) + 2 + Z.of_nat (length (s3_L2 d)) + 1 = s3_la d.
Proof. intros [] H; try destruct H; cbn; lia. Qed.
Lemma s3_fmt_range : forall v d, consts_hold LPA v -> s3_ok d -> range_ok v (diag_fmt_addr d) (s3_la d).
Proof. intros v [] CH H; try destruct H; (apply (range_ok_of_zeros_low v); [exact (zimg_of_consts v CH)| cbn; lia| cbn; lia| cbn; lia]). Qed.
Lemma s3_msg : forall d arg, s3_ok d -> diag_msg d arg = s3_L1 d ++ arg ++ s3_L2 d.
Proof. intros [] arg H; try destruct H; reflexivity. Qed.
Lemma s3_fmt_bytes3 : forall d, cells_bytes (s3_fmt d) = s3_L1 d ++ [Z_to_bv 8 37; Z_to_bv 8 115] ++ s3_L2 d ++ [Z_to_bv 8 0].
Proof. intros []; reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma str_range_ok : forall (m : word -> option byte) a n,
  bytes_at rsegs m (sh alloc_ceiling) (zeros (Z.to_nat ((2^47 - alloc_ceiling) / 8))) ->
  alloc_ceiling + 64 <= a -> 1 <= n -> a + n + 16 <= 2^47 -> range_ok m a n.
Proof.
  (* [comment removed for export] *)
  intros m a n ZS H1 H3 H2. pose proof alloc_ceiling_val as CV. pose proof alloc_ceiling_mod16 as CM.
  set (q := alloc_ceiling / 16) in *.
  assert (CQ : alloc_ceiling = 16 * q) by (pose proof (Z_div_mod_eq_full alloc_ceiling 16); lia).
  assert (D8 : alloc_ceiling / 8 = 2 * q) by (rewrite CQ; replace (16 * q) with ((2 * q) * 8) by lia; apply Z.div_mul; lia).
  assert (DK : (2^47 - alloc_ceiling) / 8 = 17592186044416 - 2 * q)
    by (rewrite CQ; replace (2^47 - 16 * q) with ((17592186044416 - 2 * q) * 8) by lia; apply Z.div_mul; lia).
  unfold sh, shadow_off, kShadowOffset in ZS. rewrite D8, DK in ZS.
  set (K := Z.to_nat (17592186044416 - 2 * q)) in ZS. assert (HK : Z.of_nat K = 17592186044416 - 2 * q) by (subst K; apply Z2Nat.id; lia).
  set (B := 2 * q + 2147450880) in ZS.
  assert (S1 : B + 8 <= sha a) by (subst B; unfold sha, shadow_off; mlia).
  assert (S2 : sha (a + n - 1) + 3 <= 17594333495296) by (unfold sha, shadow_off; mlia).
  assert (S3 : sha a <= sha (a + n - 1)) by (unfold sha, shadow_off; mlia).
  assert (BK : B + Z.of_nat K = 17594333495296) by (rewrite HK; subst B; lia).
  split. { right. lia. }
  split.
  { exists (Z.to_nat ((a + n - 1) / 8 - a / 8)), 0. split; [mlia|]. split; [|left; reflexivity].
    replace (zeros (Z.to_nat ((a + n - 1) / 8 - a / 8)) ++ [Z_to_bv 8 0])
      with (zeros (Z.to_nat ((a + n - 1) / 8 - a / 8) + 1)) by (rewrite zeros_app; reflexivity).
    replace (a / 8 + shadow_off) with (B + (sha a - B)) by (unfold sha; lia).
    apply (zeros_sub m B K); [exact ZS| lia| unfold sha, shadow_off in *; mlia]. }
  split.
  - replace (sha a - sha a mod 8) with (B + (sha a - sha a mod 8 - B)) by lia.
    apply zeros8_mapped8; [| subst B; unfold sha, shadow_off in *; mlia].
    apply (zeros_sub m B K); [exact ZS| mlia| ].
    rewrite HK. subst B. clear ZS. unfold sha, shadow_off in *. Z.div_mod_to_equations. lia.
  - replace (sha (a + n - 1) - sha (a + n - 1) mod 8) with (B + (sha (a + n - 1) - sha (a + n - 1) mod 8 - B)) by lia.
    apply zeros8_mapped8; [| subst B; unfold sha, shadow_off in *; mlia].
    apply (zeros_sub m B K); [exact ZS| mlia| ].
    rewrite HK. subst B. clear ZS. unfold sha, shadow_off in *. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma stack_zsh_bounds : forall zlo zhi,
  alloc_ceiling + 64 <= zlo -> zlo <= zhi -> zhi + 80 <= 2^47 ->
  zsh_bounds (sh alloc_ceiling) (Z.to_nat ((2^47 - alloc_ceiling) / 8)) zlo zhi
  /\ 2147446784 <= sh alloc_ceiling.   (* [comment removed for export] *)
Proof.
  (* [comment removed for export] *)
  intros zlo zhi H1 H2 H3. pose proof alloc_ceiling_val as CV. pose proof alloc_ceiling_mod16 as CM.
  set (q := alloc_ceiling / 16) in *.
  assert (CQ : alloc_ceiling = 16 * q) by (pose proof (Z_div_mod_eq_full alloc_ceiling 16); lia).
  assert (D8 : alloc_ceiling / 8 = 2 * q) by (rewrite CQ; replace (16 * q) with ((2 * q) * 8) by lia; apply Z.div_mul; lia).
  assert (DK : (2^47 - alloc_ceiling) / 8 = 17592186044416 - 2 * q)
    by (rewrite CQ; replace (2^47 - 16 * q) with ((17592186044416 - 2 * q) * 8) by lia; apply Z.div_mul; lia).
  unfold zsh_bounds, sh, sha, shadow_off, kHighShadowEnd_z, kHighMemBeg_z, SBUF_HI, kShadowOffset.
  rewrite D8, DK. rewrite Z2Nat.id by lia. change (2^47)%Z with 140737488355328%Z in *.
  OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; Z.div_mod_to_equations; lia.
Qed.

End CEIL2.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac icall_consts_in H ::= unfold fp_pre_post, fp_frame, vfu_pre_post, vfu_frame, vfu_file1, vfu_mid_post, vfu_post_post, fp_post_post,
  pcs_mid1, pcs_mid2, pcs_ret, pcu_ret, fwritex_fit_post,
  FP_DEPTH, VFB_DEPTH, PC2_DEPTH, FWRITEX_STACK, STDIO_WRITE_STACK, FP_VF_RET, VF_PC2_RET, VF_WR_RET, ARG_RET, FWX5_RET, PRINTF_CORE, INT_MAX in H;
  rewrite ?unsigned_lit in H by lia; rewrite ?length_app in H; cbn [length app Z.of_nat Nat.add Nat.sub s3_L1 s3_L2] in H; cbn_mfp_in H;
  unfold STDERR_F, STDERR_BUFP in H.

Definition keepP (P : Prop) : Prop := P.

(* [comment removed for export] *)
Ltac norm_mf_eq := lazymatch goal with |- @eq mfile ?a ?b =>
  let a' := eval cbv [mf_set_flags mf_set_buf mf_set_w mf_set_rp mf_set_mode mf_set_write_lbf
   mf_flags mf_rpos mf_rend mf_close mf_wend mf_wpos mf_mbz1 mf_wbase mf_read mf_write mf_seek mf_buf mf_bufsize
   mf_prev mf_next mf_fd mf_pipepid mf_lockcount mf_mode mf_lock mf_lbf mf_pad148 stderr0] in a in
  let b' := eval cbv [mf_set_flags mf_set_buf mf_set_w mf_set_rp mf_set_mode mf_set_write_lbf
   mf_flags mf_rpos mf_rend mf_close mf_wend mf_wpos mf_mbz1 mf_wbase mf_read mf_write mf_seek mf_buf mf_bufsize
   mf_prev mf_next mf_fd mf_pipepid mf_lockcount mf_mode mf_lock mf_lbf mf_pad148 stderr0] in b in
  change (a' = b') end.

(* [comment removed for export] *)
Ltac post_pcall :=
  let ms' := fresh "ms'" in let PO := fresh "POST" in
  intros ms' PO;
  (let T := type of PO in let h := atac_head_of T in try unfold h in PO);
  icall_consts_in PO; rewrite ?unsigned_lit in PO by lia;
  destruct_exs PO;
  let E := fresh "E" in
  lazymatch type of PO with
  | _ = _ => subst ms'
  | _ => destruct PO as [E PO]; subst ms'; try destruct_ands PO
  end;
  try (lazymatch goal with
  | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
  end).
Tactic Notation "pcall" uconstr(SPEC) "by" tactic3(side) :=
  lazymatch goal with
  | |- evt ?segs _ (MS _ _ _ _ _ ?m _) => eapply evt_cut; [ eapply SPEC; side | post_pcall ]
  end.

Section CEIL3.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Lemma stk_wr_at : forall m lo hi a n, stk rsegs m lo hi -> lo <= a -> a + n <= hi -> wr_at rsegs m a n.
Proof.
  (intros m lo hi a n; (first [ intro dR_23; dand3 dR_23 as S0 S1 S | intros (S0 & S1 & S) ]); intros Ha Hn). split; [lia|]. split; [lia|]. intros i Hi. exact (proj1 (S (a + i) ltac:(lia))).
Qed.

(* [comment removed for export] *)
Lemma rw_CB_of_parts : forall (m : word -> option byte) A (bs1 bs2 : list byte) (N : nat),
  wr_at rsegs m A (Z.of_nat N) -> bytes_at rsegs m A bs1 -> rw_cells rsegs m (A + Z.of_nat (length bs1)) [CB (length bs2) bs2] ->
  (length bs1 + length bs2 = N)%nat -> rw_cells rsegs m A [CB N (bs1 ++ bs2)].
Proof.
  intros m A bs1 bs2 N WR B1 [[W2 B2] _] L. split; [split|].
  - cbn. rewrite length_app. split; [lia| exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. cbn [cells_bytes cbytes] in B2. rewrite app_nil_r in B2.
    apply (proj2 (bytes_at_app rsegs m A bs1 bs2)). split; [exact B1| exact B2].
  - cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r. exact WR.
Qed.

End CEIL3.

(* [comment removed for export] *)
Ltac refold t v := repeat match goal with H : context [t] |- _ => progress (change t with v in H) end; try change t with v.

(* [comment removed for export] *)
Ltac sp_nest base k :=
  replace (Z_to_bv 64 (base + k)) with (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 base) + k)) by (rewrite unsigned_lit by lia; reflexivity).

Ltac fix_retpc := try lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?k)) _ _ _ _) =>
  replace (ret_pc (Z_to_bv 64 k)) with (Z_to_bv 64 k) by (symmetry; apply ret_pc_even; [lia| reflexivity]) end.

(* [comment removed for export] *)
Ltac rw_CB_from_hyp :=
  lazymatch goal with |- rw_cells _ ?m _ [CB _ _] =>
    match goal with H : rw_cells _ m _ [CB _ _] |- _ =>
      eapply rwc_eq;
      [ eapply rw_cells_recast_pf;
        [ exact H
        | cbn [cells_wf cell_wf]; split; [ pose proof (rw_CB_length _ _ _ _ _ H); rewrite ?length_skipn, ?length_app in *; cbn [length] in *; lia | exact I ]
        | cbn [cells_bytes cbytes]; rewrite ?app_nil_r; first [reflexivity | f_equal; lia] ]
      | rewrite ?length_app, ?length_skipn, ?Nat2Z.inj_add; cbn [length Z.of_nat]; lia ]
    end
  end.
(* [comment removed for export] *)
Ltac bytes_from_hyp :=
  lazymatch goal with |- bytes_at _ ?m _ ?l =>
    match goal with
    | H : bytes_at _ m _ l |- _ => eapply bytes_at_eqa; [exact H| rewrite ?length_app, ?Nat2Z.inj_add; cbn [length Z.of_nat]; lia]
    | H : bytes_at _ m _ (l ++ _) |- _ => eapply bytes_at_eqa; [exact (bytes_at_prefix _ _ _ _ _ H)| rewrite ?length_app, ?Nat2Z.inj_add; cbn [length Z.of_nat]; lia]
    end
  end.

Section Leaves.
  Context {Clg : Ceiling} {AI : AsanAlloc LPA}.   (* [comment removed for export] *)
  #[local] Notation rom := (seg_rom rsegs).

  (* [comment removed for export] *)
  Section S3.
  Variables (d : diag_fmt) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : Model) (A : AS)
            (arg slack : list byte) (pa : Z) (fe : mfile) (lo : Z) (K : TSet).
  #[local] Notation v := (aview A m).
  #[local] Notation n := (Z.of_nat (length arg)).
  #[local] Notation l1 := (Z.of_nat (length (s3_L1 d))).
  #[local] Notation l2 := (Z.of_nat (length (s3_L2 d))).
  #[local] Notation la := (s3_la d).
  #[local] Notation AF := (diag_fmt_addr d).
  Hypothesis D3 : s3_ok d.
  Hypothesis AINV : ainv A m md.
  Hypothesis MI : mem_inv rsegs v.
  Hypothesis TP : tp = cl_tp LPA.
  Hypothesis A0 : a0 = wz STDERR_F.
  Hypothesis A1 : a1 = wz (diag_fmt_addr d).
  Hypothesis A2 : a2 = wz pa.
  Hypothesis SB : bytes_at rsegs v pa (arg ++ Z_to_bv 8 0 :: slack).
  Hypothesis NIN : ~ In (Z_to_bv 8 0) arg.
  Hypothesis PALO : alloc_ceiling <= pa.
  Hypothesis PAHI : pa + Z.of_nat (length arg) + 1 + Z.of_nat (length slack) <= 2^47.
  Hypothesis SL16 : 16 <= Z.of_nat (length slack).
  Hypothesis SPP : bv_unsigned sp <= pa.
  Hypothesis PADc : (- (pa + Z.of_nat (length arg) + 1)) mod 8 <= Z.of_nat (length slack).
  Hypothesis N17 : Z.of_nat (length arg) <= 131072.
  Hypothesis ZSH : bytes_at rsegs v (sh alloc_ceiling) (zeros (Z.to_nat ((2^47 - alloc_ceiling) / 8))).
  Hypothesis FILE : file_at v STDERR_F fe.
  Hypothesis SOK : stderr_ok fe.
  Hypothesis SBUFPx : exists j8, rw_cells rsegs v STDERR_BUFP [CB 8 j8].
  Hypothesis FDL : fd_lookup (m_fds md) (wz 2) = Some (FdChannel (wz 2)).
  Hypothesis CANx : exists g, ro_cells rsegs v SSP_GUARD [C8 g].
  Hypothesis GOT : ro_cells rsegs v SSP_GOT [C8 (wz SSP_GUARD)].
  Hypothesis ST : stk rsegs v lo (bv_unsigned sp).
  Hypothesis LO : lo + FPRINTF_ICPT_STACK <= bv_unsigned sp.
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis SP16 : bv_unsigned sp mod 16 = 0.
  Hypothesis HK : K [].
  Hypothesis HKONT : forall m' md' fe' (r : word), ainv A m' md' -> md_io md md' (m_fds md) -> stderr_ok fe' -> file_at (aview A m') STDERR_F fe' ->
          forall ms', (exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
              ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 r a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                       F (ret_pc ra) fc None m' rom
              /\ munch [(bv_unsigned sp - FPRINTF_ICPT_STACK, bv_unsigned sp); (STDERR_F, STDERR_F + 152); (STDERR_BUFP, STDERR_BUFP + 8)] v (aview A m')
              /\ wmono rsegs v (aview A m') /\ mem_inv rsegs (aview A m') /\ stk rsegs (aview A m') lo (bv_unsigned sp)) ->
          srealizes rsegs (mkCfg ms' md') K.

  #[using="HKONT HK CEIL LO ST GOT CANx FDL SBUFPx SOK FILE ZSH N17 SPP SL16 PAHI PALO NIN SB A2 A1 A0 MI AINV D3 lo fe pa slack A AI Clg"] Lemma fprintf_diag_s_go :
      srealizes rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 F (wz FPRINTF_ICPT_ENTRY) fc None m rom) md)
                (t_emit (W 2 (s3_L1 d ++ arg ++ s3_L2 d)) K).
  Proof.
    destruct SBUFPx as [j8 SBUFP]. destruct CANx as [g CAN].
    pose proof FILE as FILE0. pose proof ST as ST0. pose proof MI as MI0. clear FILE ST MI. rename FILE0 into FILE. rename ST0 into ST. rename MI0 into MI.
    unfold FPRINTF_ICPT_STACK in *. subst a0 a1 a2 || (rewrite A0, A1, A2).
    pose proof (zr_word sp) as SPR; unfold inr64 in SPR. pose proof alloc_ceiling_val as CV.
    pose proof (consts_hold_ainv LPA A m md AINV) as CH.
    pose proof (fpicpt_cells_of_consts _ CH) as FPC. pose proof (asan_memcpy_cells_of_consts _ CH) as CMC. pose proof (asan_memset_cells_of_consts _ CH) as CMS.
    pose proof (strnlen_icpt_cells_of_consts _ CH) as SNC.
    pose proof (s3_fmt_range _ d CH D3) as RNGA. pose proof (s3_addr d D3) as [AD1 AD2]. (first [ pose proof ((s3_sizes d D3)) as dR_1; dand3 dR_1 as SZ1 SZ2 SZ3 | pose proof (s3_sizes d D3) as (SZ1 & SZ2 & SZ3) ]).
    pose proof (s3_fb_len d D3) as FLA.
    pose proof (bytes_at_bound _ _ _ _ SB) as PAB. rewrite length_app in PAB. cbn [length] in PAB.
    unfold STDERR_F, STDERR_BUFP, DA_Eg3i.SSP_GUARD, RA_seql.SSP_GUARD, RA_seql.GOT_SSP, SSP_GOT in *.
    pose proof (s3_la_size d) as HLA.
    (* [comment removed for export] *)
    assert (HF : ro_cells rsegs (aview A m) AF (s3_fmt d)).
    { destruct (ro_cells_image rsegs (aview A m) AF (cells_bytes (s3_fmt d)) MI
                  ltac:(clear -D3; destruct d; try destruct D3; vm_compute; reflexivity) ltac:(lia)
                  ltac:(clear -D3; destruct d; try destruct D3; cbn; lia)) as [_ B].
      cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B.
      split; [clear; destruct d; cbn; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; exact I| exact B]. }
    destruct (stack_zsh_bounds (Clg:=Clg) (bv_unsigned sp - 5408) (bv_unsigned sp - 384) ltac:(lia) ltac:(lia) ltac:(lia)) as [ZB SBL].
    assert (RNGB : range_ok (aview A m) (bv_unsigned sp - 464) 80).
    { eapply range_ok_of_zeros; [exact ZSH| exact ZB| lia| lia| lia]. }
    assert (RNGS : range_ok (aview A m) pa (n + 1)) by (apply str_range_ok; [exact ZSH| lia| lia| lia]).
    (* [comment removed for export] *)
    destruct SOK as (w & mo & -> & WOK).
    apply file_at_mode_norm in FILE. set (mo' := mo mod 2 ^ 32) in FILE.
    assert (MOR : 0 <= mo' < 2^32) by (subst mo'; apply Z.mod_pos_bound; lia).
    set (f0 := mf_set_mode (mf_set_w stderr0 w w w) mo') in FILE.
    unfold file_at, file_cells in FILE. cbn_mfp_in FILE.
    assert (SB0 : bytes_at rsegs (aview A m) pa (arg ++ [Z_to_bv 8 0])).
    { apply (bytes_at_prefix rsegs _ pa (arg ++ [Z_to_bv 8 0]) slack). rewrite <- app_assoc. exact SB. }
    assert (SB15 : bytes_at rsegs (aview A m) pa (arg ++ Z_to_bv 8 0 :: firstn 15 slack)).
    { apply (bytes_at_prefix rsegs _ pa (arg ++ Z_to_bv 8 0 :: firstn 15 slack) (skipn 15 slack)).
      rewrite <- app_assoc. cbn [app]. rewrite firstn_skipn. exact SB. }
    assert (SL15 : Z.of_nat (length (firstn 15 slack)) = 15) by (rewrite length_firstn; lia).
    assert (PAD15 : padP pa n (Z.of_nat (length (firstn 15 slack)))) by (unfold padP; rewrite SL15; try (generalize alloc_ceiling_val); clear -PADc; Z.div_mod_to_equations; lia).
    assert (SF0 : sfS AF la (bv_unsigned sp - 464) 80 (sh alloc_ceiling) (Z.to_nat ((2^47 - alloc_ceiling) / 8))
                      (bv_unsigned sp - 480 - PC2_DEPTH) (bv_unsigned sp - 480 + 96) pa (n + 1) (aview A m)).
    { unfold sfS, sfF, PC2_DEPTH. replace (bv_unsigned sp - 480 - 4928) with (bv_unsigned sp - 5408) by lia.
      replace (bv_unsigned sp - 480 + 96) with (bv_unsigned sp - 384) by lia.
      exact (conj (conj CMC (conj CMS (conj RNGA (conj RNGB (conj ZSH (conj ZB SBL)))))) (conj SNC RNGS)). }
    pose proof SBUFP as SBUFP0. lazymatch type of SBUFP0 with ?T => change T with (keepP T) in SBUFP0 end.
    pose proof (stk_wr_at _ _ _ (bv_unsigned sp - 8192) 8192 ST ltac:(lia) ltac:(lia)) as WRS.
    pose proof (stk_wr_at _ _ _ (bv_unsigned sp - 464) 80 ST ltac:(lia) ltac:(lia)) as WRB.
    (* [comment removed for export] *)
    pose proof (munch_refl [(bv_unsigned sp - 8192, bv_unsigned sp); (0xad928, 0xad928 + 152); (0x608ae0, 0x608ae0 + 8)] (aview A m)) as MU.
    pose proof (wmono_refl rsegs (aview A m)) as WM.
    assert (CF : client_fpx (L:=LPA) A (aview A m) [(bv_unsigned sp - 8192, bv_unsigned sp); (0xad928, 0xad928 + 152); (0x608ae0, 0x608ae0 + 8)]).
    { cbn. split. { left. split; [| exact I]. left. split; [lia|]. split; [lia|]. eapply (stk_mapped (L:=LPA)); [exact ST | exact CEIL | lia | lia]. }
      split. { right. split; [cbn; lia|]. split; [cbn; lia|]. intros a Ha. cbn [cl_static cl_shared LPA]. unfold pa_static, pa_shared. lia. }
      split; [| exact I]. right. split; [cbn; lia|]. split; [cbn; lia|]. intros a Ha. cbn [cl_static cl_shared LPA]. unfold pa_static, pa_shared. lia. }
    assert (HW : wfok [(bv_unsigned sp - 8192, bv_unsigned sp); (0xad928, 0xad928 + 152); (0x608ae0, 0x608ae0 + 8)]) by solve_wfok.
    ago AINV. fold_cl_segs.
    (* [comment removed for export] *)
    assert (H1 : lo <= bv_unsigned sp - FP_DEPTH) by (unfold FP_DEPTH; lia).
    assert (H2 : alloc_ceiling <= lo) by exact CEIL.   (* [comment removed for export] *)
    assert (H3 : bv_unsigned sp <= 2^47) by lia.
    assert (H4 : AF + la <= RO_TOP) by (unfold RO_TOP; lia).
    assert (VL : fpsh_low_s AF la pa (n + 1) (aview A m)) by (split; [split; [exact FPC| exact RNGA]| exact RNGS]).
    try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_ZSH); icall (fp_pre_s ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo AF la 0xad928 (s3_fmt d) (s3_fb d) H1 H2 H3 H4
             (s3_fb_bytes d D3) FLA (s3_pcm d D3)
             t0 t1 t2 _ _ _ a3 a4 a5 a6 a7 t3 t4 t5 t6 (aview A m) pa arg eq_refl eq_refl eq_refl ST HF SB0 NIN ltac:(lia) SPP ltac:(lia) VL MI)
      by (first [mf_easm | reflexivity | lia]).
    lazymatch goal with H : stk rsegs ?mx lo _ |- _ => rename H into ST1;
      lazymatch goal with H2 : rw_cells rsegs mx (bv_unsigned sp + -112) _ |- _ => rename H2 into FPF1 end;
      lazymatch goal with H3 : mem_inv rsegs mx |- _ => rename H3 into MI1 end end.
    clear POST.
    (* [comment removed for export] *)
    assert (Q1 : lo <= bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -112)) - VFB_DEPTH) by (rewrite unsigned_lit by lia; unfold VFB_DEPTH; lia).
    assert (Q2 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -112)) <= 2^47) by (rewrite unsigned_lit by lia; lia).
    assert (F1 : mf_flags f0 = 5) by reflexivity.
    assert (F2 : mf_lock f0 = -1) by reflexivity.
    assert (F3 : mf_bufsize f0 = 0) by reflexivity.
    assert (F4 : 0 < mf_buf f0 < 2^63) by (subst f0; cbn_mfp; unfold stderr0; cbn [mf_buf]; unfold STDERR_BUFP; lia).
    assert (F5 : 0 <= mf_mode f0 < 2^32) by (subst f0; cbn_mfp; exact MOR).
    assert (F6 : FILE_LO <= 0xad928 /\ 0xad928 + 152 <= FILE_HI) by (unfold FILE_LO, FILE_HI; lia).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
    icall (vfu_pre (s3_fmt d) la (s3_la_size d) (s3_pc1 d D3) towrite_ok
             (Z_to_bv 64 FP_VF_RET) (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp (Z_to_bv 64 AF) (Z_to_bv 64 0xad928) (Z_to_bv 64 (bv_unsigned sp + -48)) s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
             lo AF 0xad928 (bv_unsigned sp + -48) g f0
             Q1 Q2 H2 H4 F1 F2 F3 F5 F6
             _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mx eq_refl eq_refl eq_refl)
      by (first [ rewrite ?unsigned_lit by lia; mf_easm | split; mf_easm
                | subst f0; unfold file_at, file_cells; cbn_mfp; mf_easm | reflexivity | lia ]
          || match goal with |- ?G => idtac "VFSIDE-FAIL" G end)
    end.
    lazymatch goal with H : stk rsegs ?mx lo _ |- _ => rename H into ST2;
      (first [ dand5 PC0 as APC2 AP2 JB2 JR2 VFR2 | destruct PC0 as (APC2 & AP2 & JB2 & JR2 & VFR2) ]); rename POST into FILE2; rename MI into MI2 end.
    pose proof (rw_CB_length _ _ _ _ _ JB2) as JBL.
    (* [comment removed for export] *)
    pose proof (proj2 (proj1 (proj2 (proj1 (rw_cells_app rsegs _ _ [_;_;_;_;_;_;_;_] _) FPF1)))) as VAB.
    cbn [cells_size csize Nat.add cells_bytes cbytes] in VAB. rewrite app_nil_r in VAB.
    match type of VAB with bytes_at _ _ ?ax _ => replace ax with (bv_unsigned sp + -48)%Z in VAB by (cbn; lia) end.
    rewrite <- u64s_6 in VAB.
    (* [comment removed for export] *)
    assert (R1 : lo <= bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -112 + -368)) - PC2_DEPTH) by (rewrite unsigned_lit by lia; unfold PC2_DEPTH; lia).
    assert (R2 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -112 + -368)) + 368 <= bv_unsigned sp + -48) by (rewrite unsigned_lit by lia; lia).
    assert (R3 : IMG_LO <= AF) by (unfold IMG_LO; lia).
    assert (R4 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -112 + -368)) + 368 <= pa) by (rewrite unsigned_lit by lia; lia).
    assert (R5 : pa + n + 1 + Z.of_nat (length (firstn 15 slack)) < 2^47) by lia.
    assert (R6 : n <= 2^17) by lia.
    lazymatch type of FILE2 with file_at ?mx _ ?f1 =>
    assert (G1 : mf_flags f1 = 5) by reflexivity;
    assert (G2 : mf_wbase f1 = Z_to_bv 64 (mf_buf f1)) by reflexivity;
    assert (G3 : mf_wpos f1 = Z_to_bv 64 (mf_buf f1 + Z.of_nat (@length byte []))) by (cbn_mfp; cbn [length Z.of_nat]; rewrite Z.add_0_r; reflexivity);
    assert (G4 : mf_wend f1 = Z_to_bv 64 (mf_buf f1 + mf_bufsize f1)) by reflexivity;
    assert (G5 : 0 < mf_buf f1) by (cbn_mfp; lia);
    assert (G6 : mf_buf f1 + mf_bufsize f1 < 2^47) by (cbn_mfp; lia);
    assert (G7 : 0 <= mf_bufsize f1 < 2^31) by (cbn_mfp; lia);
    assert (G8 : mf_lbf f1 < 0) by (subst f0; cbn_mfp; unfold stderr0; cbn [mf_lbf]; lia);
    assert (G9 : -2^31 <= mf_lbf f1) by (subst f0; cbn_mfp; unfold stderr0; cbn [mf_lbf]; lia);
    assert (G10 : Z.of_nat (@length byte []) + l1 <= mf_bufsize f1) by (cbn_mfp; cbn [length Z.of_nat]; lia);
    lazymatch type of JB2 with rw_cells _ _ _ [CB 80 ?jb] =>
      assert (G11 : Z.of_nat (@length byte []) + Z.of_nat (length jb) = mf_bufsize f1) by (cbn_mfp; cbn [length Z.of_nat]; lia) end;
    assert (G12 : 0xad928 + 152 <= mf_buf f1 \/ mf_buf f1 + mf_bufsize f1 <= 0xad928) by (cbn_mfp; lia);
    assert (G13 : mf_buf f1 + mf_bufsize f1 <= lo \/ bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -112 + -368)) + 16 <= mf_buf f1) by (cbn_mfp; rewrite unsigned_lit by lia; lia);
    assert (G14 : (SBUF_LO <= mf_buf f1 /\ mf_buf f1 + mf_bufsize f1 <= SBUF_HI) \/ kHighMemBeg_z <= mf_buf f1) by (cbn_mfp; unfold kHighMemBeg_z; lia);
    assert (G15 : mf_buf f1 + mf_bufsize f1 <= bv_unsigned sp + -48) by (cbn_mfp; lia);
    assert (G16 : mf_buf f1 + mf_bufsize f1 <= pa) by (cbn_mfp; lia)
    end.
    pose proof (fok_sfS AF la (bv_unsigned sp - 464) 80 _ _ (bv_unsigned sp - 480 - PC2_DEPTH) (bv_unsigned sp - 480 + 96) pa (n + 1)
                  ltac:(lia) ltac:(lia) ltac:(lia) _ _ _ MU HW SF0) as SF1.
    assert (EA3 : Z_to_bv 64 (bv_unsigned sp + -112 + -272) = Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -112 + -368)) + 96)) by (f_equal; rewrite unsigned_lit by lia; lia).
    assert (EA4 : Z_to_bv 64 (bv_unsigned sp + -112 + -104) = Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -112 + -368)) + 264)) by (f_equal; rewrite unsigned_lit by lia; lia).
    try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_APC2); try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_JB2); lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
    lazymatch type of FILE2 with file_at _ _ ?f1 =>
    lazymatch type of JB2 with rw_cells _ _ _ [CB 80 ?jb] =>
    icall (pcs_head (Z_to_bv 64 VF_PC2_RET) (Z_to_bv 64 (bv_unsigned sp + -112 + -368)) gp tp (Z_to_bv 64 0xad928) (Z_to_bv 64 AF) (Z_to_bv 64 6325272) (Z_to_bv 64 1) (Z_to_bv 64 (mf_buf f0)) (Z_to_bv 64 5) s6 s7 s8 s9 s10 s11 F fc
             d lo AF 0xad928 (bv_unsigned sp + -48) pa g f1 [] jb arg (firstn 15 slack) [a3; a4; a5; a6; a7]
             (sh alloc_ceiling) (Z.to_nat ((2^47 - alloc_ceiling) / 8))
             fwritex_fit_ok D3 R1 H2 R2 R3 H4 G1 G2 G3 G4 G5 G6 G7 G8 G9 G10 G11 F6 G12 G13 G14 G15 R4 R5 NIN PAD15 R6 G16
             _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mx eq_refl eq_refl eq_refl EA3 EA4)
      by (first [ rewrite ?unsigned_lit by lia; mf_easm | split; mf_easm
                | apply bytes_at_nil; cbn_mfp; lia
                | lazymatch goal with |- rw_cells _ _ _ [CB (length ?jb') _] => cbn_mfp; cbn [length Z.of_nat]; rewrite ?Z.add_0_r;
                    eapply rw_cells_recast_pf; [exact JB2| cbn; split; [reflexivity| exact I] | reflexivity] end
                | rewrite ?unsigned_lit by lia; f_equal; lia
                | lazymatch goal with |- sfS _ _ _ _ _ _ _ _ _ _ _ => cbn_mfp; rewrite ?unsigned_lit by lia;
                    replace (bv_unsigned sp + -112 + -368 - PC2_DEPTH) with (bv_unsigned sp - 480 - PC2_DEPTH) by lia;
                    replace (bv_unsigned sp + -112 + -368 + 96) with (bv_unsigned sp - 480 + 96) by lia;
                    replace (bv_unsigned sp + -112 + -352) with (bv_unsigned sp - 464) by lia; exact SF1 end
                | reflexivity | lia ]
          || match goal with |- ?G => idtac "PCSSIDE-FAIL" G end)
    end end end.
    clear SF1.
    lazymatch goal with H : stk rsegs ?mx lo _ |- _ => rename H into ST3; rename PC0 into FRo3; rename PC1 into FRa3; rename PC2 into FRs3;
      rename PC3 into FILE3; rename PC4 into BUF3; rename PC5 into RST3; rename PC6 into APC3; rename PC7 into SBc3; rename PC8 into SSP3; rename POST into SF3; rename MI into MI3 end.
    
    replace (bv_unsigned sp + -112 + -352 + Z.of_nat 0 + l1) with (bv_unsigned sp + -112 + -352 + l1) in * by lia.
    replace (bv_unsigned sp + -48 + 8) with (bv_unsigned sp + -40) in APC3 by lia.
    lazymatch type of RST3 with rw_cells _ _ _ [CB _ (skipn ?k ?jb)] => rewrite <- (length_skipn k jb) in RST3 end.
    unfold pc_lits in FRo3. unfold pc_saved in FRs3. rewrite ?unsigned_lit in FRo3 by lia.
    assert (SRCA : forall mq, bytes_at rsegs mq pa (arg ++ Z_to_bv 8 0 :: firstn 15 slack) -> bytes_at rsegs mq pa arg).
    { intros mq Hq. exact (bytes_at_prefix rsegs mq pa arg _ Hq). }
    (* [comment removed for export] *)
    destruct (Z.le_gt_cases (l1 + n) 80) as [FIT1 | FL1].
    - (* [comment removed for export] *)
      assert (RNG4 : forall mq, sfS AF la (bv_unsigned sp + -112 + -352) 80 (sh alloc_ceiling) (Z.to_nat ((2^47 - alloc_ceiling) / 8))
                        (bv_unsigned sp + -112 + -368 - 4928) (bv_unsigned sp + -112 + -368 + 96) pa (n + 1) mq ->
                      n = 0 \/ (range_ok mq pa n /\ range_ok mq (bv_unsigned sp + -112 + -352 + l1) n)).
      { intros mq SFq. destruct (Z.eq_dec n 0) as [N0|N0]; [left; exact N0| right]. split.
        - eapply range_ok_sub; [exact (proj2 (proj2 SFq))| lia| lia| lia].
        - eapply (sfF_buf_range _ _ _ _ _ _ _ _ _ _ _ (proj1 SFq)); lia. }
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      lazymatch type of FILE3 with file_at _ _ ?f3 =>
      lazymatch type of RST3 with rw_cells _ _ _ [CB _ ?rst] =>
      icall (fwritex_fit_ok _ _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc mx 0xad928
               f3 (s3_L1 d) arg rst pa lo)
        by (cbn_mfp; unfold FWRITEX_STACK; 
            first [ reflexivity
                  | rewrite ?unsigned_lit by lia; mf_easm
                  | left; first [lia | subst f0; cbn_mfp; unfold stderr0; cbn [mf_lbf]; lia]
                  | apply SRCA; assumption
                  | lazymatch goal with |- memcpy_icpt_cells _ => exact (proj1 (proj1 SF3)) end
                  | lazymatch goal with |- (_ = 0 \/ _)%type => apply RNG4; exact SF3 end
                  | eapply rwc_eq; [mf_easm| lia]
                  | eapply bytes_at_eqa; [mf_easm| lia]
                  | f_equal; lia
                  | rewrite ?length_skipn; lia
                  | rewrite ?unsigned_lit by lia; lia ]
            || match goal with |- ?G => idtac "W2C4-FAIL" G end)
      end end end.
      
      repeat match goal with H : context [skipn ?a (skipn ?b ?r)] |- _ => rewrite skipn_skipn in H end.
      repeat match goal with H : rw_cells rsegs _ _ [CB (length (skipn ?a ?r) - ?b)%nat _] |- _ => rewrite length_skipn, <- Nat.sub_add_distr, <- length_skipn in H end.
      (* [comment removed for export] *)
      sp_nest (bv_unsigned sp + -112 + -368) (-544).
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      lazymatch goal with FI : file_at mx 710952 ?fx |- _ =>
      lazymatch goal with Rq : rw_cells rsegs mx _ [CB _ (skipn _ ?jb)] |- _ =>
      let RM := fresh "RM" in assert (RM : Z.of_nat (@length byte []) + l1 <= mf_bufsize fx) by (cbn_mfp; cbn [length Z.of_nat]; lia);
      pcall (pcs_mid (Z_to_bv 64 VF_PC2_RET) (Z_to_bv 64 (bv_unsigned sp + -112 + -368)) gp tp (Z_to_bv 64 0xad928) (Z_to_bv 64 AF) (Z_to_bv 64 6325272) (Z_to_bv 64 1) (Z_to_bv 64 (mf_buf f0)) (Z_to_bv 64 5) s6 s7 s8 s9 s10 s11 F fc
               d lo AF 0xad928 pa g fx [] jb arg (firstn 15 slack) D3 R3 H4 RM F6 R6
               _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mx _ _ _ fx)
        by (first [ rewrite ?unsigned_lit by lia; mf_easm | split; mf_easm | cbn_mfp; reflexivity
                  | lazymatch goal with |- rw_cells _ _ _ (CB 40 _ :: pc_lits _) => unfold pc_lits; rewrite ?unsigned_lit by lia; mf_easm end
                  | cbn_mfp; lia ]
            || match goal with |- ?G => idtac "MID-FAIL" G end)
      end end end.
      
      (* [comment removed for export] *)
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      lazymatch goal with HFq : ro_cells rsegs mx AF (s3_fmt d) |- _ =>
        pose proof (proj2 HFq) as SRC5; rewrite s3_fmt_bytes3 in SRC5;
        apply bytes_at_app_r in SRC5; apply bytes_at_app_r in SRC5; apply bytes_at_prefix in SRC5;
        cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in SRC5
      end end.
      (* [comment removed for export] *)
      destruct (Z.le_gt_cases (l1 + n + l2) 80) as [FIT2 | FL2].
      + (* [comment removed for export] *)
        lazymatch goal with MUq : munch _ (aview A m) ?mx |- _ =>
          pose proof (fok_sfS AF la (bv_unsigned sp - 464) 80 _ _ (bv_unsigned sp - 480 - PC2_DEPTH) (bv_unsigned sp - 480 + 96) pa (n + 1)
                        ltac:(lia) ltac:(lia) ltac:(lia) _ _ _ MUq HW SF0) as SF4 end.
        try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_POST); lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
        lazymatch goal with FI : file_at mx 710952 ?fx |- _ =>
        lazymatch goal with Rq : rw_cells rsegs mx _ [CB _ (skipn ?k ?jb)] |- _ =>
        icall (fwritex_fit_ok _ _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc mx 0xad928
                 fx (s3_L1 d ++ arg) (s3_L2 d) (skipn k jb) (AF + l1 + 2) lo)
          by (cbn_mfp; unfold FWRITEX_STACK; rewrite ?length_app;
              first [ reflexivity
                    | rewrite ?unsigned_lit by lia; mf_easm
                    | left; first [lia | subst f0; cbn_mfp; unfold stderr0; cbn [mf_lbf]; lia]
                    | lazymatch goal with |- memcpy_icpt_cells _ => exact (proj1 (proj1 SF4)) end
                    | lazymatch goal with |- (_ = 0 \/ _)%type => right; split;
                        [ eapply (sfF_fmt_range _ _ _ _ _ _ _ _ _ _ _ (proj1 SF4)); lia | eapply (sfF_buf_range _ _ _ _ _ _ _ _ _ _ _ (proj1 SF4)); lia ] end
                    | rw_CB_from_hyp
                    | bytes_from_hyp
                    | f_equal; lia
                    | rewrite ?length_skipn; lia
                    | rewrite ?unsigned_lit by lia; lia ]
              || match goal with |- ?G => idtac "W2C5-FAIL" G end)
        end end end.
        repeat match goal with H : context [skipn ?a (skipn ?b ?r)] |- _ => rewrite skipn_skipn in H end.
        (* [comment removed for export] *)
        sp_nest (bv_unsigned sp + -112 + -368) (-544).
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
        lazymatch goal with FI : file_at mx 710952 ?fx |- _ =>
        lazymatch goal with Rq : rw_cells rsegs mx _ [CB _ (skipn _ ?jb)] |- _ =>
        let RM := fresh "RM" in assert (RM : Z.of_nat (@length byte []) + l1 <= mf_bufsize fx) by (cbn_mfp; cbn [length Z.of_nat]; lia);
        pcall (pcs_tail (Z_to_bv 64 VF_PC2_RET) (Z_to_bv 64 (bv_unsigned sp + -112 + -368)) gp tp (Z_to_bv 64 0xad928) (Z_to_bv 64 AF) (Z_to_bv 64 6325272) (Z_to_bv 64 1) (Z_to_bv 64 (mf_buf f0)) (Z_to_bv 64 5) s6 s7 s8 s9 s10 s11 F fc
                 d lo AF 0xad928 pa g fx [] jb arg (firstn 15 slack) D3 R1 H4 RM F6 R6
                 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mx _ _ _)
          by (first [ rewrite ?unsigned_lit by lia; mf_easm | split; mf_easm
                    | lazymatch goal with |- rw_cells _ _ _ (CB 40 _ :: pc_lits _) => unfold pc_lits; rewrite ?unsigned_lit by lia; mf_easm end
                    | cbn_mfp; cbn [length Z.of_nat]; lia ]
              || match goal with |- ?G => idtac "TAIL-FAIL" G end)
        end end end.
        sp_nest (bv_unsigned sp + -112) (-368).
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
        lazymatch goal with FI : file_at mx 710952 ?fx |- _ =>
        pcall (vfu_mid (s3_fmt d) (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp s6 s7 s8 s9 s10 s11 F fc lo AF 0xad928 f0 F4
                 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mx fx)
          by (first [ rewrite ?unsigned_lit by lia; mf_easm | cbn_mfp; reflexivity | subst f0; cbn_mfp; unfold stderr0; cbn; reflexivity ]
              || match goal with |- ?G => idtac "VMID-FAIL" G end)
        end end.
        lazymatch goal with H : stk rsegs ?mx lo _ |- _ => rename H into ST8; lazymatch goal with FI : file_at mx 710952 _ |- _ => rename FI into FILE8 end;
          lazymatch goal with Bq : bytes_at rsegs mx (bv_unsigned sp + -112 + -352) _ |- _ => rename Bq into BUF8 end;
          lazymatch goal with Mq : mem_inv rsegs mx |- _ => rename Mq into MI8 end end.
        (* [comment removed for export] *)
        astopx AINV MU WM CF. rename m0 into m1. rename md0 into md1. rename AINV0 into AINV1.
        pose proof (as_minv LPA A m1 md1 AINV1) as [_ HH1].
        (first [ pose proof ((sbm_io md md1 SBM)) as dR_3; dand3 dR_3 as FS1 FDS1 _ | pose proof (sbm_io md md1 SBM) as (FS1 & FDS1 & _) ]).
        rewrite <- (app_nil_r (s3_L1 d ++ arg ++ s3_L2 d)). rewrite <- app_assoc in BUF8.
        lazymatch type of FILE8 with file_at _ _ ?f8 =>
        eapply (stdio_write_ok _ _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 md1 A
                  0xad928 f8 (s3_L1 d ++ arg ++ s3_L2 d) [] 0 _ lo K AINV1 MI8) end.
        all: lazymatch goal with
             | |- forall m' md', ainv _ _ _ -> _ => idtac
             | |- ?G => first [ reflexivity
                              | rewrite ?unsigned_lit by lia; mf_easm
                              | right; subst f0; cbn_mfp; unfold stderr0; cbn [mf_fd]; reflexivity
                              | unfold img_client; cbn [cl_rw_lo cl_image_hi LPA]; split; [cbn; lia| split; [cbn; lia| intros aa Ha; cbn [cl_static cl_shared LPA]; unfold pa_static, pa_shared; lia]]
                              | subst f0; cbn_mfp; unfold stderr0; cbn [mf_fd]; rewrite FDS1; exact FDL
                              | cbn_mfp; rewrite ?length_app, ?Nat2Z.inj_add; cbn [length Z.of_nat]; first [reflexivity | f_equal; lia | lia]
                              | cbn_mfp; bytes_from_hyp
                              | apply bytes_at_nil; lia
                              | eexists; mf_easm
                              | exact HK
                              | unfold STDIO_WRITE_STACK; rewrite ?unsigned_lit by lia; cbn_mfp; rewrite ?length_app; cbn [length Z.of_nat]; lia ]
                        || idtac "W3-FAIL" G
             end.
        intros m2 md2 AINV2 IO2 FILE9 ms' PO2.
        destruct_exs PO2. destruct PO2 as [E [MU2 [WM2 [MI9 ST9]]]]. subst ms'.
        unfold STDIO_WRITE_STACK in MU2, ST9. rewrite ?unsigned_lit in MU2 by lia. rewrite ?unsigned_lit in ST9 by lia.
        cbn_mfp_in FILE9.
        try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_FRs3); transport_after_call rsegs (aview A m1) (aview A m2) MU2 WM2. clear MU2 WM2 MI8.
        (first [ dand3 IO2 as FS2 FDS2 _ | destruct IO2 as (FS2 & FDS2 & _) ]).

        (* [comment removed for export] *)
        pose proof (munch_refl [(bv_unsigned sp - 8192, bv_unsigned sp); (0xad928, 0xad928 + 152)] (aview A m2)) as MUe.
        pose proof (wmono_refl rsegs (aview A m2)) as WMe.
        assert (CFe : client_fpx (L:=LPA) A (aview A m2) [(bv_unsigned sp - 8192, bv_unsigned sp); (0xad928, 0xad928 + 152)]).
        { cbn. split. { left. split; [| exact I]. left. split; [lia|]. split; [lia|].
            lazymatch goal with H : wr_at rsegs (aview A m2) (bv_unsigned sp - 8192) 8192 |- _ =>
              replace (bv_unsigned sp - (bv_unsigned sp - 8192)) with 8192 by lia; eapply (wr_at_mapped LPA); [exact H| apply (off_image_stack LPA); lia] end. }
          split; [| exact I]. right. split; [cbn; lia|]. split; [cbn; lia|]. intros aa Ha. cbn [cl_static cl_shared LPA]. unfold pa_static, pa_shared. lia. }
        ago AINV2. fold_cl_segs. fix_retpc.
        sp_nest (bv_unsigned sp + -112) (-368).
        try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_AP2); try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_APC3); try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_BUF3); try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_BUF8); try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_FRa3); try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_FRo3); try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_JR2); try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_PC1); try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_POST0); try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_VFR2); lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
        lazymatch goal with FI : file_at mx 710952 ?f9 |- _ =>
        lazymatch goal with Rq : rw_cells rsegs mx _ [CB _ (skipn ?k ?jb)] |- _ =>
        lazymatch goal with JRq : rw_cells rsegs mx (bv_unsigned sp + -112 + -272) [CB 168 ?jr] |- _ =>
        lazymatch goal with Bq : bytes_at rsegs mx (bv_unsigned sp + -112 + -352) ?pd |- _ =>
        icall (vfu_post (s3_fmt d) (Z_to_bv 64 FP_VF_RET) (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp (Z_to_bv 64 AF) (Z_to_bv 64 0xad928) (Z_to_bv 64 (bv_unsigned sp + -48)) s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
                 lo 0xad928 (bv_unsigned sp + -48) g f0 Q1 H2 F6
                 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mx f9 (pd ++ skipn k jb) jr (bv_unsigned sp + -112 + -352) _)
          by (first [ rewrite ?unsigned_lit by lia; mf_easm | split; mf_easm | cbn_mfp; reflexivity | cbn_mfp; lia
                    | lazymatch goal with |- rw_cells _ _ _ [CB 80 _] => rewrite ?unsigned_lit by lia;
                        eapply rwc_eq;
                        [ eapply rw_CB_of_parts; [ exact WRB | bytes_from_hyp | rw_CB_from_hyp
                                                 | lazymatch goal with H : rw_cells rsegs _ _ [CB _ (skipn k jb)] |- _ => pose proof (rw_CB_length _ _ _ _ _ H) end;
                                                   rewrite ?length_app, ?length_skipn in *; cbn [length] in *; lia ]
                        | lia ] end ]
              || match goal with |- ?G => idtac "VPOST-FAIL" G end)
        end end end end end.
        lazymatch goal with H : stk rsegs ?mx lo (bv_unsigned sp + -112) |- _ => rename H into STy;
          lazymatch goal with FI : file_at mx 710952 _ |- _ => rename FI into FILEy end;
          lazymatch goal with Mq : mem_inv rsegs mx |- _ => rename Mq into MIy end end.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
        pcall (fp_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo (s3_fb d) H1
                 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mx _ _ _ _ _ _ _)
          by (first [ rewrite ?unsigned_lit by lia; mf_easm ] || match goal with |- ?G => idtac "FPOST-FAIL" G end)
        end.
        lazymatch goal with H : stk rsegs ?mx lo (bv_unsigned sp) |- _ => rename H into STz end.
        (* [comment removed for export] *)
        astopx AINV2 MUe WMe CFe. rename m0 into mz. rename md0 into mdz. rename AINV0 into AINVz.
        pose proof (as_minv LPA A mz mdz AINVz) as [_ HHz].
        (first [ pose proof ((sbm_io _ mdz SBM0)) as dR_5; dand3 dR_5 as FSz FDSz _ | pose proof (sbm_io _ mdz SBM0) as (FSz & FDSz & _) ]).
        lazymatch type of FILEy with file_at _ _ ?fz => eapply (HKONT mz mdz fz _ AINVz) end.
        { split; [| split; [| exact HHz]]; congruence. }
        { lazymatch goal with |- stderr_ok ?fz => eexists w0, _; split; [| left; reflexivity]; subst f0; norm_mf_eq; reflexivity end. }
        { exact FILEy. }
        hot_eexists_all. split; [reflexivity|].
        split. { first [ exact MU | eapply munch_trans; [exact MU|]; eapply munch_weaken; [| exact MUe]; unfold sub_fp; cbn [outside]; intros; lia ]. }
        split. { first [ exact WM | eapply wmono_trans; [exact WM| exact WMe] ]. }
        split; [exact MIy| exact STz].
      + (* [comment removed for export] *)
        lazymatch goal with H : stk rsegs ?mx lo _ |- _ => rename H into ST6;
          lazymatch goal with FI : file_at mx 710952 _ |- _ => rename FI into FILE6 end;
          lazymatch goal with Bq : bytes_at rsegs mx (bv_unsigned sp + -112 + -352) (s3_L1 d ++ arg) |- _ => rename Bq into BUF6 end;
          lazymatch goal with Mq : mem_inv rsegs mx |- _ => rename Mq into MI6 end end.
        astopx AINV MU WM CF. rename m0 into m1. rename md0 into md1. rename AINV0 into AINV1.
        pose proof (as_minv LPA A m1 md1 AINV1) as [_ HH1].
        (first [ pose proof ((sbm_io md md1 SBM)) as dR_6; dand3 dR_6 as FS1 FDS1 _ | pose proof (sbm_io md md1 SBM) as (FS1 & FDS1 & _) ]).
        rewrite (app_assoc (s3_L1 d) arg (s3_L2 d)).
        lazymatch type of FILE6 with file_at _ _ ?f6 =>
        eapply (fwritex_flush_ok _ _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 md1 A
                  0xad928 f6 (s3_L1 d ++ arg) (s3_L2 d) (AF + l1 + 2) lo K AINV1 MI6) end.
        all: lazymatch goal with
             | |- forall m' md', ainv _ _ _ -> _ => idtac
             | |- ?G => first [ reflexivity
                              | rewrite ?unsigned_lit by lia; mf_easm
                              | right; subst f0; cbn_mfp; unfold stderr0; cbn [mf_fd]; reflexivity
                              | subst f0; cbn_mfp; unfold stderr0; cbn [mf_write]; reflexivity
                              | unfold img_client; cbn [cl_rw_lo cl_image_hi LPA]; split; [cbn; lia| split; [cbn; lia| intros aa Ha; cbn [cl_static cl_shared LPA]; unfold pa_static, pa_shared; lia]]
                              | subst f0; cbn_mfp; unfold stderr0; cbn [mf_fd]; rewrite FDS1; exact FDL
                              | cbn_mfp; rewrite ?length_app, ?Nat2Z.inj_add; cbn [length Z.of_nat]; first [reflexivity | f_equal; lia | lia]
                              | cbn_mfp; bytes_from_hyp
                              | eexists; mf_easm
                              | exact HK
                              | left; cbn_mfp; rewrite ?length_app, ?Nat2Z.inj_add; cbn [length Z.of_nat]; lia
                              | right; unfold FWRITEX_STACK; rewrite ?unsigned_lit by lia; cbn_mfp; lia
                              | unfold FWRITEX_STACK; rewrite ?unsigned_lit by lia; cbn_mfp; rewrite ?length_app; cbn [length Z.of_nat]; lia ]
                        || idtac "W2B6-FAIL" G
             end.
        intros m2 md2 AINV2 IO2 FILE9 ms' PO2.
        destruct_exs PO2. destruct PO2 as [E [MU2 [WM2 [MI9 ST9]]]]. subst ms'.
        unfold STDIO_WRITE_STACK, FWRITEX_STACK in MU2, ST9. rewrite ?unsigned_lit in MU2 by lia. rewrite ?unsigned_lit in ST9 by lia.
        cbn_mfp_in FILE9.
        lazymatch type of MU2 with munch _ (aview A ?ma) (aview A ?mb) => transport_after_call rsegs (aview A ma) (aview A mb) MU2 WM2 end. clear MU2 WM2.
        try match goal with H : mem_inv rsegs (aview A ?mq), H2 : mem_inv rsegs (aview A m2) |- _ => lazymatch mq with m2 => fail | _ => clear H end end.
        (first [ dand3 IO2 as FS2 FDS2 _ | destruct IO2 as (FS2 & FDS2 & _) ]).
        (* [comment removed for export] *)
        ago AINV2. fold_cl_segs. fix_retpc.
        sp_nest (bv_unsigned sp + -112 + -368) (-544).
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
        lazymatch type of FILE9 with file_at _ _ ?fx =>
        lazymatch goal with Rq : rw_cells rsegs mx _ [CB _ (skipn _ ?jb)] |- _ =>
        let RM := fresh "RM" in assert (RM : Z.of_nat (@length byte []) + l1 <= mf_bufsize fx) by (cbn_mfp; cbn [length Z.of_nat]; lia);
        pcall (pcs_tail (Z_to_bv 64 VF_PC2_RET) (Z_to_bv 64 (bv_unsigned sp + -112 + -368)) gp tp (Z_to_bv 64 0xad928) (Z_to_bv 64 AF) (Z_to_bv 64 6325272) (Z_to_bv 64 1) (Z_to_bv 64 (mf_buf f0)) (Z_to_bv 64 5) s6 s7 s8 s9 s10 s11 F fc
                 d lo AF 0xad928 pa g fx [] jb arg (firstn 15 slack) D3 R1 H4 RM F6 R6
                 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mx _ _ _)
          by (first [ rewrite ?unsigned_lit by lia; mf_easm | split; mf_easm
                    | lazymatch goal with |- rw_cells _ _ _ (CB 40 _ :: pc_lits _) => unfold pc_lits; rewrite ?unsigned_lit by lia; mf_easm end
                    | cbn_mfp; cbn [length Z.of_nat]; lia ]
              || match goal with |- ?G => idtac "TAIL2-FAIL" G end)
        end end end.
        sp_nest (bv_unsigned sp + -112) (-368).
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
        lazymatch type of FILE9 with file_at _ _ ?fx =>
        pcall (vfu_mid (s3_fmt d) (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp s6 s7 s8 s9 s10 s11 F fc lo AF 0xad928 f0 F4
                 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mx fx)
          by (first [ rewrite ?unsigned_lit by lia; mf_easm | cbn_mfp; reflexivity | subst f0; cbn_mfp; unfold stderr0; cbn; reflexivity ]
              || match goal with |- ?G => idtac "VMID2-FAIL" G end)
        end end.
        lazymatch goal with H : stk rsegs ?mx lo _ |- _ => rename H into ST8 end.
        astop0 AINV2. rename m0 into m3. rename md0 into md3. rename AINV0 into AINV3.
        pose proof (as_minv LPA A m3 md3 AINV3) as [_ HH3].
        (first [ pose proof ((sbm_io md2 md3 SBM0)) as dR_8; dand3 dR_8 as FS3 FDS3 _ | pose proof (sbm_io md2 md3 SBM0) as (FS3 & FDS3 & _) ]).
        (* [comment removed for export] *)
        lazymatch type of FILE9 with file_at _ _ ?f8 =>
        eapply (stdio_write_zero_ok _ _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m3 md3 A 0xad928 f8 lo K AINV3 MI9) end.
        all: lazymatch goal with
             | |- forall m' md', ainv _ _ _ -> _ => idtac
             | |- ?G => first [ reflexivity
                              | rewrite ?unsigned_lit by lia; mf_easm
                              | right; subst f0; cbn_mfp; unfold stderr0; cbn [mf_fd]; reflexivity
                              | unfold img_client; cbn [cl_rw_lo cl_image_hi LPA]; split; [cbn; lia| split; [cbn; lia| intros aa Ha; cbn [cl_static cl_shared LPA]; unfold pa_static, pa_shared; lia]]
                              | subst f0; cbn_mfp; unfold stderr0; cbn [mf_fd]; rewrite FDS3, FDS2, FDS1; exact FDL
                              | cbn_mfp; reflexivity
                              | eexists; mf_easm
                              | unfold STDIO_WRITE_STACK; rewrite ?unsigned_lit by lia; cbn_mfp; lia ]
                        || idtac "W3Z-FAIL" G
             end.
        try clear FILE9. try clear ST9.
        intros m4 md4 AINV4 IO4 FILE9 ms' POb.
        destruct_exs POb. destruct POb as [Eb [MUb [WMb [MIb ST9]]]]. subst ms'.
        unfold STDIO_WRITE_STACK, FWRITEX_STACK in MUb, ST9. rewrite ?unsigned_lit in MUb by lia. rewrite ?unsigned_lit in ST9 by lia.
        cbn_mfp_in FILE9.
        try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_FRs3); lazymatch type of MUb with munch _ (aview A ?ma) (aview A ?mb) => transport_after_call rsegs (aview A ma) (aview A mb) MUb WMb end. clear MUb WMb.
        try match goal with H : mem_inv rsegs (aview A ?mq), H2 : mem_inv rsegs (aview A m4) |- _ => lazymatch mq with m4 => fail | _ => clear H end end.
        (first [ dand3 IO4 as FS4 FDS4 _ | destruct IO4 as (FS4 & FDS4 & _) ]).

        (* [comment removed for export] *)
        pose proof (munch_refl [(bv_unsigned sp - 8192, bv_unsigned sp); (0xad928, 0xad928 + 152)] (aview A m4)) as MUe.
        pose proof (wmono_refl rsegs (aview A m4)) as WMe.
        assert (CFe : client_fpx (L:=LPA) A (aview A m4) [(bv_unsigned sp - 8192, bv_unsigned sp); (0xad928, 0xad928 + 152)]).
        { cbn. split. { left. split; [| exact I]. left. split; [lia|]. split; [lia|].
            lazymatch goal with H : wr_at rsegs (aview A m4) (bv_unsigned sp - 8192) 8192 |- _ =>
              replace (bv_unsigned sp - (bv_unsigned sp - 8192)) with 8192 by lia; eapply (wr_at_mapped LPA); [exact H| apply (off_image_stack LPA); lia] end. }
          split; [| exact I]. right. split; [cbn; lia|]. split; [cbn; lia|]. intros aa Ha. cbn [cl_static cl_shared LPA]. unfold pa_static, pa_shared. lia. }
        ago AINV4. fold_cl_segs. fix_retpc.
        sp_nest (bv_unsigned sp + -112) (-368).
        try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_AP2); try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_APC3); try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_BUF3); try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_BUF6); try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_FRa3); try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_FRo3); try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_JR2); try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_POST); try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_VFR2); lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
        lazymatch goal with FI : file_at mx 710952 ?f9 |- _ =>
        lazymatch goal with Rq : rw_cells rsegs mx _ [CB _ (skipn ?k ?jb)] |- _ =>
        lazymatch goal with JRq : rw_cells rsegs mx (bv_unsigned sp + -112 + -272) [CB 168 ?jr] |- _ =>
        lazymatch goal with Bq : bytes_at rsegs mx (bv_unsigned sp + -112 + -352) ?pd |- _ =>
        icall (vfu_post (s3_fmt d) (Z_to_bv 64 FP_VF_RET) (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp (Z_to_bv 64 AF) (Z_to_bv 64 0xad928) (Z_to_bv 64 (bv_unsigned sp + -48)) s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
                 lo 0xad928 (bv_unsigned sp + -48) g f0 Q1 H2 F6
                 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mx f9 (pd ++ skipn k jb) jr (bv_unsigned sp + -112 + -352) _)
          by (first [ rewrite ?unsigned_lit by lia; mf_easm | split; mf_easm | cbn_mfp; reflexivity | cbn_mfp; lia
                    | lazymatch goal with |- rw_cells _ _ _ [CB 80 _] => rewrite ?unsigned_lit by lia;
                        eapply rwc_eq;
                        [ eapply rw_CB_of_parts; [ exact WRB | bytes_from_hyp | rw_CB_from_hyp
                                                 | lazymatch goal with H : rw_cells rsegs _ _ [CB _ (skipn k jb)] |- _ => pose proof (rw_CB_length _ _ _ _ _ H) end;
                                                   rewrite ?length_app, ?length_skipn in *; cbn [length] in *; lia ]
                        | lia ] end ]
              || match goal with |- ?G => idtac "VPOST-FAIL" G end)
        end end end end end.
        lazymatch goal with H : stk rsegs ?mx lo (bv_unsigned sp + -112) |- _ => rename H into STy;
          lazymatch goal with FI : file_at mx 710952 _ |- _ => rename FI into FILEy end;
          lazymatch goal with Mq : mem_inv rsegs mx |- _ => rename Mq into MIy end end.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
        pcall (fp_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo (s3_fb d) H1
                 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mx _ _ _ _ _ _ _)
          by (first [ rewrite ?unsigned_lit by lia; mf_easm ] || match goal with |- ?G => idtac "FPOST-FAIL" G end)
        end.
        lazymatch goal with H : stk rsegs ?mx lo (bv_unsigned sp) |- _ => rename H into STz end.
        (* [comment removed for export] *)
        astopx AINV4 MUe WMe CFe. rename m0 into mz. rename md0 into mdz. rename AINV0 into AINVz.
        pose proof (as_minv LPA A mz mdz AINVz) as [_ HHz].
        (first [ pose proof ((sbm_io _ mdz SBM1)) as dR_10; dand3 dR_10 as FSz FDSz _ | pose proof (sbm_io _ mdz SBM1) as (FSz & FDSz & _) ]).
        lazymatch type of FILEy with file_at _ _ ?fz => eapply (HKONT mz mdz fz _ AINVz) end.
        { split; [| split; [| exact HHz]]; congruence. }
        { lazymatch goal with |- stderr_ok ?fz => eexists w0, _; split; [| left; reflexivity]; subst f0; norm_mf_eq; reflexivity end. }
        { exact FILEy. }
        hot_eexists_all. split; [reflexivity|].
        split. { first [ exact MU | eapply munch_trans; [exact MU|]; eapply munch_weaken; [| exact MUe]; unfold sub_fp; cbn [outside]; intros; lia ]. }
        split. { first [ exact WM | eapply wmono_trans; [exact WM| exact WMe] ]. }
        split; [exact MIy| exact STz].
    - (* [comment removed for export] *)
      lazymatch goal with H : stk rsegs ?mx lo _ |- _ => idtac end.
      astopx AINV MU WM CF. rename m0 into m1. rename md0 into md1. rename AINV0 into AINV1.
      pose proof (as_minv LPA A m1 md1 AINV1) as [_ HH1].
      (first [ pose proof ((sbm_io md md1 SBM)) as dR_11; dand3 dR_11 as FS1 FDS1 _ | pose proof (sbm_io md md1 SBM) as (FS1 & FDS1 & _) ]).
      apply (srz_conseq rsegs _ (t_emit (W 2 (s3_L1 d ++ arg)) (t_emit (W 2 (s3_L2 d)) K))).
      2:{ rewrite (app_assoc (s3_L1 d) arg (s3_L2 d)). rewrite (W_app 2 (s3_L1 d ++ arg) (s3_L2 d)). first [apply t_emit_app | apply t_eq_sym; apply t_emit_app]. }
      lazymatch type of FILE3 with file_at _ _ ?f3 =>
      eapply (fwritex_flush_ok _ _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 md1 A
                0xad928 f3 (s3_L1 d) arg pa lo (t_emit (W 2 (s3_L2 d)) K) AINV1 MI3) end.
      all: lazymatch goal with
           | |- forall m' md', ainv _ _ _ -> _ => idtac
           | |- ?G => first [ reflexivity
                            | rewrite ?unsigned_lit by lia; mf_easm
                            | right; subst f0; cbn_mfp; unfold stderr0; cbn [mf_fd]; reflexivity
                            | subst f0; cbn_mfp; unfold stderr0; cbn [mf_write]; reflexivity
                            | unfold img_client; cbn [cl_rw_lo cl_image_hi LPA]; split; [cbn; lia| split; [cbn; lia| intros aa Ha; cbn [cl_static cl_shared LPA]; unfold pa_static, pa_shared; lia]]
                            | subst f0; cbn_mfp; unfold stderr0; cbn [mf_fd]; rewrite FDS1; exact FDL
                            | cbn_mfp; rewrite ?length_app, ?Nat2Z.inj_add; cbn [length Z.of_nat]; first [reflexivity | f_equal; lia | lia]
                            | cbn_mfp; bytes_from_hyp
                            | apply SRCA; assumption
                            | eexists; mf_easm
                            | apply t_emit_has_nil
                            | left; cbn_mfp; rewrite ?length_app, ?Nat2Z.inj_add; cbn [length Z.of_nat]; lia
                            | right; unfold FWRITEX_STACK; rewrite ?unsigned_lit by lia; cbn_mfp; lia
                            | unfold FWRITEX_STACK; rewrite ?unsigned_lit by lia; cbn_mfp; rewrite ?length_app; cbn [length Z.of_nat]; lia ]
                      || idtac "W2B4-FAIL" G
           end.
        intros m2 md2 AINV2 IO2 FILE9 ms' PO2.
        destruct_exs PO2. destruct PO2 as [E [MU2 [WM2 [MI9 ST9]]]]. subst ms'.
        unfold STDIO_WRITE_STACK, FWRITEX_STACK in MU2, ST9. rewrite ?unsigned_lit in MU2 by lia. rewrite ?unsigned_lit in ST9 by lia.
        cbn_mfp_in FILE9.
        lazymatch type of MU2 with munch _ (aview A ?ma) (aview A ?mb) => transport_after_call rsegs (aview A ma) (aview A mb) MU2 WM2 end. clear MU2 WM2.
        try match goal with H : mem_inv rsegs (aview A ?mq), H2 : mem_inv rsegs (aview A m2) |- _ => lazymatch mq with m2 => fail | _ => clear H end end.
        (first [ dand3 IO2 as FS2 FDS2 _ | destruct IO2 as (FS2 & FDS2 & _) ]).
      (* [comment removed for export] *)
      pose proof (munch_refl [(bv_unsigned sp - 8192, bv_unsigned sp); (0xad928, 0xad928 + 152)] (aview A m2)) as MU5.
      pose proof (wmono_refl rsegs (aview A m2)) as WM5.
      assert (CF5 : client_fpx (L:=LPA) A (aview A m2) [(bv_unsigned sp - 8192, bv_unsigned sp); (0xad928, 0xad928 + 152)]).
      { cbn. split. { left. split; [| exact I]. left. split; [lia|]. split; [lia|].
          lazymatch goal with H : wr_at rsegs (aview A m2) (bv_unsigned sp - 8192) 8192 |- _ =>
            replace (bv_unsigned sp - (bv_unsigned sp - 8192)) with 8192 by lia; eapply (wr_at_mapped LPA); [exact H| apply (off_image_stack LPA); lia] end. }
        split; [| exact I]. right. split; [cbn; lia|]. split; [cbn; lia|]. intros aa Ha. cbn [cl_static cl_shared LPA]. unfold pa_static, pa_shared. lia. }
      assert (HW5 : wfok [(bv_unsigned sp - 8192, bv_unsigned sp); (0xad928, 0xad928 + 152)]) by solve_wfok.
      ago AINV2. fold_cl_segs. fix_retpc.
      sp_nest (bv_unsigned sp + -112 + -368) (-544).
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      lazymatch type of FILE9 with file_at _ _ ?fx =>
      lazymatch goal with Rq : rw_cells rsegs mx _ [CB _ (skipn _ ?jb)] |- _ =>
      let RM := fresh "RM" in assert (RM : Z.of_nat (@length byte []) + l1 <= mf_bufsize fx) by (cbn_mfp; cbn [length Z.of_nat]; lia);
      pcall (pcs_mid (Z_to_bv 64 VF_PC2_RET) (Z_to_bv 64 (bv_unsigned sp + -112 + -368)) gp tp (Z_to_bv 64 0xad928) (Z_to_bv 64 AF) (Z_to_bv 64 6325272) (Z_to_bv 64 1) (Z_to_bv 64 (mf_buf f0)) (Z_to_bv 64 5) s6 s7 s8 s9 s10 s11 F fc
               d lo AF 0xad928 pa g fx [] jb arg (firstn 15 slack) D3 R3 H4 RM F6 R6
               _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mx _ _ _ fx)
        by (first [ rewrite ?unsigned_lit by lia; mf_easm | split; mf_easm | cbn_mfp; reflexivity
                  | lazymatch goal with |- rw_cells _ _ _ (CB 40 _ :: pc_lits _) => unfold pc_lits; rewrite ?unsigned_lit by lia; mf_easm end
                  | cbn_mfp; cbn [length Z.of_nat]; lia ]
            || match goal with |- ?G => idtac "MID3-FAIL" G end)
      end end end.
      (* [comment removed for export] *)
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      lazymatch goal with HFq : ro_cells rsegs mx AF (s3_fmt d) |- _ =>
        pose proof (proj2 HFq) as SRC5; rewrite s3_fmt_bytes3 in SRC5;
        apply bytes_at_app_r in SRC5; apply bytes_at_app_r in SRC5; apply bytes_at_prefix in SRC5;
        cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in SRC5
      end end.
      (* [comment removed for export] *)
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      lazymatch goal with Rq : rw_cells rsegs mx _ [CB _ (skipn ?k ?jb)] |- _ =>
        assert (JB80 : rw_cells rsegs mx (bv_unsigned sp + -112 + -352) [CB 80 (s3_L1 d ++ skipn k jb)]);
        [ eapply rwc_eq; [ eapply rw_CB_of_parts; [ exact WRB | bytes_from_hyp | rw_CB_from_hyp
                                                   | pose proof (rw_CB_length _ _ _ _ _ Rq); rewrite ?length_app, ?length_skipn in *; cbn [length] in *; lia ]
                         | lia ]
        | assert (JBX : rw_cells rsegs mx (bv_unsigned sp + -112 + -352) [CB (length (s3_L1 d ++ skipn k jb)) (s3_L1 d ++ skipn k jb)])
            by (eapply rw_cells_recast_pf; [exact JB80 | cbn [cells_wf cell_wf]; split; [reflexivity| exact I] | reflexivity]) ] end end.
      lazymatch goal with MUq : munch _ (aview A m) ?mcur |- _ =>
        pose proof (fok_sfS AF la (bv_unsigned sp - 464) 80 _ _ (bv_unsigned sp - 480 - PC2_DEPTH) (bv_unsigned sp - 480 + 96) pa (n + 1)
                      ltac:(lia) ltac:(lia) ltac:(lia) _ _ _ MUq HW SF0) as SF7 end.
      try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_BUF3); try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_JB80); try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_JBX); try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_RST3); lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      lazymatch goal with FI : file_at mx 710952 ?fx |- _ =>
      lazymatch type of JBX with rw_cells _ _ _ [CB _ ?rst] =>
      icall (fwritex_fit_ok _ _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc mx 0xad928
               fx [] (s3_L2 d) rst (AF + l1 + 2) lo)
        by (cbn_mfp; unfold FWRITEX_STACK; rewrite ?length_app;
            first [ reflexivity
                  | rewrite ?unsigned_lit by lia; mf_easm
                  | left; first [lia | subst f0; cbn_mfp; unfold stderr0; cbn [mf_lbf]; lia]
                  | lazymatch goal with |- memcpy_icpt_cells _ => exact (proj1 (proj1 SF7)) end
                  | lazymatch goal with |- (_ = 0 \/ _)%type => right; cbn [length Z.of_nat]; rewrite ?Z.add_0_r; split;
                      [ eapply (sfF_fmt_range _ _ _ _ _ _ _ _ _ _ _ (proj1 SF7)); lia | eapply (sfF_buf_range _ _ _ _ _ _ _ _ _ _ _ (proj1 SF7)); lia ] end
                  | apply bytes_at_nil; lia
                  | lazymatch goal with |- rw_cells _ _ _ [CB _ (_ ++ _)] => cbn [length Z.of_nat]; rewrite ?Z.add_0_r;
                      eapply rw_cells_recast_pf; [exact JB80 | cbn [cells_wf cell_wf]; split; [rewrite ?length_app; reflexivity| exact I] | cbn [cells_bytes cbytes]; reflexivity] end
                  | bytes_from_hyp
                  | f_equal; lia
                  | rewrite ?length_skipn; pose proof (rw_CB_length _ _ _ _ _ JBX); rewrite ?length_app, ?length_skipn in *; cbn [length] in *; lia
                  | rewrite ?unsigned_lit by lia; lia ]
            || match goal with |- ?G => idtac "W2C7-FAIL" G end)
      end end end.
      (* [comment removed for export] *)
      sp_nest (bv_unsigned sp + -112 + -368) (-544).
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      lazymatch goal with FI : file_at mx 710952 ?fx |- _ =>
      lazymatch type of JBL with length ?jb = _ =>
      let RM := fresh "RM" in assert (RM : Z.of_nat (@length byte []) + l1 <= mf_bufsize fx) by (cbn_mfp; cbn [length Z.of_nat]; lia);
      pcall (pcs_tail (Z_to_bv 64 VF_PC2_RET) (Z_to_bv 64 (bv_unsigned sp + -112 + -368)) gp tp (Z_to_bv 64 0xad928) (Z_to_bv 64 AF) (Z_to_bv 64 6325272) (Z_to_bv 64 1) (Z_to_bv 64 (mf_buf f0)) (Z_to_bv 64 5) s6 s7 s8 s9 s10 s11 F fc
               d lo AF 0xad928 pa g fx [] jb arg (firstn 15 slack) D3 R1 H4 RM F6 R6
               _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mx _ _ _)
        by (first [ rewrite ?unsigned_lit by lia; mf_easm | split; mf_easm
                  | lazymatch goal with |- rw_cells _ _ _ (CB 40 _ :: pc_lits _) => unfold pc_lits; rewrite ?unsigned_lit by lia; mf_easm end
                  | cbn_mfp; cbn [length Z.of_nat]; lia ]
            || match goal with |- ?G => idtac "TAIL3-FAIL" G end)
      end end end.
      sp_nest (bv_unsigned sp + -112) (-368).
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      lazymatch goal with FI : file_at mx 710952 ?fx |- _ =>
      pcall (vfu_mid (s3_fmt d) (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp s6 s7 s8 s9 s10 s11 F fc lo AF 0xad928 f0 F4
               _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mx fx)
        by (first [ rewrite ?unsigned_lit by lia; mf_easm | cbn_mfp; reflexivity | subst f0; cbn_mfp; unfold stderr0; cbn; reflexivity ]
            || match goal with |- ?G => idtac "VMID3-FAIL" G end)
      end end.
      lazymatch goal with H : stk rsegs ?mx lo _ |- _ => rename H into ST8; lazymatch goal with FI : file_at mx 710952 _ |- _ => rename FI into FILE8 end;
        lazymatch goal with Bq : bytes_at rsegs mx (bv_unsigned sp + -112 + -352) _ |- _ => rename Bq into BUF8 end;
        lazymatch goal with Mq : mem_inv rsegs mx |- _ => rename Mq into MI8 end end.
      astopx AINV2 MU5 WM5 CF5. rename m0 into m3. rename md0 into md3. rename AINV0 into AINV3.
      pose proof (as_minv LPA A m3 md3 AINV3) as [_ HH3].
      (first [ pose proof ((sbm_io md2 md3 SBM0)) as dR_13; dand3 dR_13 as FS3 FDS3 _ | pose proof (sbm_io md2 md3 SBM0) as (FS3 & FDS3 & _) ]).
      (* [comment removed for export] *)
      lazymatch goal with |- srealizes _ _ (t_emit (W 2 ?x) ?k) => replace (t_emit (W 2 x) k) with (t_emit (W 2 (x ++ [])) k) by (rewrite app_nil_r; reflexivity) end.
      lazymatch type of FILE8 with file_at _ _ ?f8 =>
      eapply (stdio_write_ok _ _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m3 md3 A
                0xad928 f8 (s3_L2 d) [] 0 _ lo K AINV3 MI8) end.
      all: lazymatch goal with
           | |- forall m' md', ainv _ _ _ -> _ => idtac
           | |- ?G => first [ reflexivity
                            | rewrite ?unsigned_lit by lia; mf_easm
                            | right; subst f0; cbn_mfp; unfold stderr0; cbn [mf_fd]; reflexivity
                            | unfold img_client; cbn [cl_rw_lo cl_image_hi LPA]; split; [cbn; lia| split; [cbn; lia| intros aa Ha; cbn [cl_static cl_shared LPA]; unfold pa_static, pa_shared; lia]]
                            | subst f0; cbn_mfp; unfold stderr0; cbn [mf_fd]; rewrite FDS3, FDS2, FDS1; exact FDL
                            | cbn_mfp; rewrite ?length_app, ?Nat2Z.inj_add; cbn [length Z.of_nat]; first [reflexivity | f_equal; lia | lia]
                            | cbn_mfp; bytes_from_hyp
                            | apply bytes_at_nil; lia
                            | eexists; mf_easm
                            | exact HK
                            | unfold STDIO_WRITE_STACK; rewrite ?unsigned_lit by lia; cbn_mfp; rewrite ?length_app; cbn [length Z.of_nat]; lia ]
                      || idtac "W3L-FAIL" G
           end.
        try clear FILE9. try clear ST9.
        intros m4 md4 AINV4 IO4 FILE9 ms' POb.
        destruct_exs POb. destruct POb as [Eb [MUb [WMb [MIb ST9]]]]. subst ms'.
        unfold STDIO_WRITE_STACK, FWRITEX_STACK in MUb, ST9. rewrite ?unsigned_lit in MUb by lia. rewrite ?unsigned_lit in ST9 by lia.
        cbn_mfp_in FILE9.
        try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_FRs3); lazymatch type of MUb with munch _ (aview A ?ma) (aview A ?mb) => transport_after_call rsegs (aview A ma) (aview A mb) MUb WMb end. clear MUb WMb.
        try match goal with H : mem_inv rsegs (aview A ?mq), H2 : mem_inv rsegs (aview A m4) |- _ => lazymatch mq with m4 => fail | _ => clear H end end.
        (first [ dand3 IO4 as FS4 FDS4 _ | destruct IO4 as (FS4 & FDS4 & _) ]).

        (* [comment removed for export] *)
        pose proof (munch_refl [(bv_unsigned sp - 8192, bv_unsigned sp); (0xad928, 0xad928 + 152)] (aview A m4)) as MUe.
        pose proof (wmono_refl rsegs (aview A m4)) as WMe.
        assert (CFe : client_fpx (L:=LPA) A (aview A m4) [(bv_unsigned sp - 8192, bv_unsigned sp); (0xad928, 0xad928 + 152)]).
        { cbn. split. { left. split; [| exact I]. left. split; [lia|]. split; [lia|].
            lazymatch goal with H : wr_at rsegs (aview A m4) (bv_unsigned sp - 8192) 8192 |- _ =>
              replace (bv_unsigned sp - (bv_unsigned sp - 8192)) with 8192 by lia; eapply (wr_at_mapped LPA); [exact H| apply (off_image_stack LPA); lia] end. }
          split; [| exact I]. right. split; [cbn; lia|]. split; [cbn; lia|]. intros aa Ha. cbn [cl_static cl_shared LPA]. unfold pa_static, pa_shared. lia. }
        ago AINV4. fold_cl_segs. fix_retpc.
        sp_nest (bv_unsigned sp + -112) (-368).
        try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_AP2); try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_APC3); try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_BUF8); try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_FRa3); try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_FRo3); try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_JR2); try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_POST); try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_VFR2); lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
        lazymatch goal with FI : file_at mx 710952 ?f9 |- _ =>
        lazymatch goal with Rq : rw_cells rsegs mx _ [CB _ (skipn ?k ?jb)] |- _ =>
        lazymatch goal with JRq : rw_cells rsegs mx (bv_unsigned sp + -112 + -272) [CB 168 ?jr] |- _ =>
        lazymatch goal with Bq : bytes_at rsegs mx (bv_unsigned sp + -112 + -352) ?pd |- _ =>
        icall (vfu_post (s3_fmt d) (Z_to_bv 64 FP_VF_RET) (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp (Z_to_bv 64 AF) (Z_to_bv 64 0xad928) (Z_to_bv 64 (bv_unsigned sp + -48)) s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
                 lo 0xad928 (bv_unsigned sp + -48) g f0 Q1 H2 F6
                 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mx f9 (pd ++ skipn k jb) jr (bv_unsigned sp + -112 + -352) _)
          by (first [ rewrite ?unsigned_lit by lia; mf_easm | split; mf_easm | cbn_mfp; reflexivity | cbn_mfp; lia
                    | lazymatch goal with |- rw_cells _ _ _ [CB 80 _] => rewrite ?unsigned_lit by lia;
                        eapply rwc_eq;
                        [ eapply rw_CB_of_parts; [ exact WRB | bytes_from_hyp | rw_CB_from_hyp
                                                 | lazymatch goal with H : rw_cells rsegs _ _ [CB _ (skipn k jb)] |- _ => pose proof (rw_CB_length _ _ _ _ _ H) end;
                                                   rewrite ?length_app, ?length_skipn in *; cbn [length] in *; lia ]
                        | lia ] end ]
              || match goal with |- ?G => idtac "VPOST-FAIL" G end)
        end end end end end.
        lazymatch goal with H : stk rsegs ?mx lo (bv_unsigned sp + -112) |- _ => rename H into STy;
          lazymatch goal with FI : file_at mx 710952 _ |- _ => rename FI into FILEy end;
          lazymatch goal with Mq : mem_inv rsegs mx |- _ => rename Mq into MIy end end.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
        pcall (fp_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo (s3_fb d) H1
                 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mx _ _ _ _ _ _ _)
          by (first [ rewrite ?unsigned_lit by lia; mf_easm ] || match goal with |- ?G => idtac "FPOST-FAIL" G end)
        end.
        lazymatch goal with H : stk rsegs ?mx lo (bv_unsigned sp) |- _ => rename H into STz end.
        (* [comment removed for export] *)
        astopx AINV4 MUe WMe CFe. rename m0 into mz. rename md0 into mdz. rename AINV0 into AINVz.
        pose proof (as_minv LPA A mz mdz AINVz) as [_ HHz].
        (first [ pose proof ((sbm_io _ mdz SBM1)) as dR_15; dand3 dR_15 as FSz FDSz _ | pose proof (sbm_io _ mdz SBM1) as (FSz & FDSz & _) ]).
        lazymatch type of FILEy with file_at _ _ ?fz => eapply (HKONT mz mdz fz _ AINVz) end.
        { split; [| split; [| exact HHz]]; congruence. }
        { lazymatch goal with |- stderr_ok ?fz => eexists w0, _; split; [| left; reflexivity]; subst f0; norm_mf_eq; reflexivity end. }
        { exact FILEy. }
        hot_eexists_all. split; [reflexivity|].
        split. { first [ exact MU | eapply munch_trans; [exact MU|]; eapply munch_weaken; [| exact MUe]; unfold sub_fp; cbn [outside]; intros; lia ]. }
        split. { first [ exact WM | eapply wmono_trans; [exact WM| exact WMe] ]. }
        split; [exact MIy| exact STz].
  Qed.
  End S3.

  (* [comment removed for export] *)
  Section SU.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : Model) (A : AS)
            (fe : mfile) (lo : Z) (K : TSet).
  #[local] Notation v := (aview A m).
  #[local] Notation AF := 0x19c83.
  Hypothesis AINV : ainv A m md.
  Hypothesis MI : mem_inv rsegs v.
  Hypothesis TP : tp = cl_tp LPA.
  Hypothesis A0 : a0 = wz STDERR_F.
  Hypothesis A1 : a1 = wz AF.
  Hypothesis A2 : a2 = wz 67108864.
  Hypothesis ZSH : bytes_at rsegs v (sh alloc_ceiling) (zeros (Z.to_nat ((2^47 - alloc_ceiling) / 8))).
  Hypothesis FILE : file_at v STDERR_F fe.
  Hypothesis SOK : stderr_ok fe.
  Hypothesis SBUFPx : exists j8, rw_cells rsegs v STDERR_BUFP [CB 8 j8].
  Hypothesis FDL : fd_lookup (m_fds md) (wz 2) = Some (FdChannel (wz 2)).
  Hypothesis CANx : exists g, ro_cells rsegs v SSP_GUARD [C8 g].
  Hypothesis GOT : ro_cells rsegs v SSP_GOT [C8 (wz SSP_GUARD)].
  Hypothesis ST : stk rsegs v lo (bv_unsigned sp).
  Hypothesis LO : lo + FPRINTF_ICPT_STACK <= bv_unsigned sp.
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis SP16 : bv_unsigned sp mod 16 = 0.
  Hypothesis SPHI : bv_unsigned sp <= 2^47.
  Hypothesis HK : K [].
  Hypothesis HKONT : forall m' md' fe' (r : word), ainv A m' md' -> md_io md md' (m_fds md) -> stderr_ok fe' -> file_at (aview A m') STDERR_F fe' ->
          forall ms', (exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
              ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 r a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                       F (ret_pc ra) fc None m' rom
              /\ munch [(bv_unsigned sp - FPRINTF_ICPT_STACK, bv_unsigned sp); (STDERR_F, STDERR_F + 152); (STDERR_BUFP, STDERR_BUFP + 8)] v (aview A m')
              /\ wmono rsegs v (aview A m') /\ mem_inv rsegs (aview A m') /\ stk rsegs (aview A m') lo (bv_unsigned sp)) ->
          srealizes rsegs (mkCfg ms' md') K.

  Lemma U_fbytes : cells_bytes FMT_REFUSED = FMTB_REFUSED ++ [Z_to_bv 8 0].
  Proof. vm_compute. reflexivity. Qed.
  Lemma U_fla : Z.of_nat (length FMTB_REFUSED) + 1 = 33.
  Proof. reflexivity. Qed.
  Lemma U_hla : Z.of_nat (cells_size FMT_REFUSED) = 33.
  Proof. reflexivity. Qed.
  Lemma U_msg : msg_refused = U_MSG.
  Proof. vm_compute. reflexivity. Qed.
  Lemma U_len : Z.of_nat (length U_MSG) = 38.
  Proof. reflexivity. Qed.

  #[using="HKONT HK SPHI CEIL LO ST GOT CANx FDL SBUFPx SOK FILE ZSH A2 A1 A0 MI AINV lo fe A AI Clg"] Lemma fprintf_diag_u_go :
      srealizes rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 F (wz FPRINTF_ICPT_ENTRY) fc None m rom) md)
                (t_emit (W 2 msg_refused) K).
  Proof.
    destruct SBUFPx as [j8 SBUFP]. destruct CANx as [g CAN].
    pose proof FILE as FILE0. pose proof ST as ST0. pose proof MI as MI0. clear FILE ST MI. rename FILE0 into FILE. rename ST0 into ST. rename MI0 into MI.
    unfold FPRINTF_ICPT_STACK in *. subst a0 a1 a2 || (rewrite A0, A1, A2).
    pose proof (zr_word sp) as SPR; unfold inr64 in SPR. pose proof alloc_ceiling_val as CV.
    pose proof (consts_hold_ainv LPA A m md AINV) as CH.
    pose proof (fpicpt_cells_of_consts _ CH) as FPC. pose proof (asan_memcpy_cells_of_consts _ CH) as CMC. pose proof (asan_memset_cells_of_consts _ CH) as CMS.
    assert (RNGA : range_ok (aview A m) AF 33) by exact (fmt_range_of_consts _ CH DF_refused).
    pose proof U_hla as HLA. (* [comment removed for export] *)
    pose proof U_len as ULEN.
    unfold STDERR_F, STDERR_BUFP, DA_Eg3i.SSP_GUARD, RA_seql.SSP_GUARD, RA_seql.GOT_SSP, SSP_GOT in *.
    (* [comment removed for export] *)
    assert (HF : ro_cells rsegs (aview A m) AF FMT_REFUSED).
    { destruct (ro_cells_image rsegs (aview A m) AF (cells_bytes FMT_REFUSED) MI ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)) as [_ B].
      cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B.
      split; [clear; cbn; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; exact I| exact B]. }
    destruct (stack_zsh_bounds (Clg:=Clg) (bv_unsigned sp - 5408) (bv_unsigned sp - 384) ltac:(lia) ltac:(lia) ltac:(lia)) as [ZB SBL].
    assert (RNGB : range_ok (aview A m) (bv_unsigned sp - 464) 80).
    { eapply range_ok_of_zeros; [exact ZSH| exact ZB| lia| lia| lia]. }
    (* [comment removed for export] *)
    destruct SOK as (w & mo & -> & WOK).
    apply file_at_mode_norm in FILE. set (mo' := mo mod 2 ^ 32) in FILE.
    assert (MOR : 0 <= mo' < 2^32) by (subst mo'; apply Z.mod_pos_bound; lia).
    set (f0 := mf_set_mode (mf_set_w stderr0 w w w) mo') in FILE.
    unfold file_at, file_cells in FILE. cbn_mfp_in FILE.
    assert (SF0 : sfF AF 33 (bv_unsigned sp - 464) 80 (sh alloc_ceiling) (Z.to_nat ((2^47 - alloc_ceiling) / 8))
                      (bv_unsigned sp - 480 - PC2_DEPTH) (bv_unsigned sp - 480 + 96) (aview A m)).
    { unfold sfF, PC2_DEPTH. replace (bv_unsigned sp - 480 - 4928) with (bv_unsigned sp - 5408) by lia.
      replace (bv_unsigned sp - 480 + 96) with (bv_unsigned sp - 384) by lia.
      exact (conj CMC (conj CMS (conj RNGA (conj RNGB (conj ZSH (conj ZB SBL)))))). }
    pose proof SBUFP as SBUFP0. lazymatch type of SBUFP0 with ?T => change T with (keepP T) in SBUFP0 end.
    pose proof (stk_wr_at _ _ _ (bv_unsigned sp - 8192) 8192 ST ltac:(lia) ltac:(lia)) as WRS.
    pose proof (stk_wr_at _ _ _ (bv_unsigned sp - 464) 80 ST ltac:(lia) ltac:(lia)) as WRB.
    (* [comment removed for export] *)
    pose proof (munch_refl [(bv_unsigned sp - 8192, bv_unsigned sp); (0xad928, 0xad928 + 152); (0x608ae0, 0x608ae0 + 8)] (aview A m)) as MU.
    pose proof (wmono_refl rsegs (aview A m)) as WM.
    assert (CF : client_fpx (L:=LPA) A (aview A m) [(bv_unsigned sp - 8192, bv_unsigned sp); (0xad928, 0xad928 + 152); (0x608ae0, 0x608ae0 + 8)]).
    { cbn. split. { left. split; [| exact I]. left. split; [lia|]. split; [lia|]. eapply (stk_mapped (L:=LPA)); [exact ST | exact CEIL | lia | lia]. }
      split. { right. split; [cbn; lia|]. split; [cbn; lia|]. intros a Ha. cbn [cl_static cl_shared LPA]. unfold pa_static, pa_shared. lia. }
      split; [| exact I]. right. split; [cbn; lia|]. split; [cbn; lia|]. intros a Ha. cbn [cl_static cl_shared LPA]. unfold pa_static, pa_shared. lia. }
    assert (HW : wfok [(bv_unsigned sp - 8192, bv_unsigned sp); (0xad928, 0xad928 + 152); (0x608ae0, 0x608ae0 + 8)]) by solve_wfok.
    ago AINV. fold_cl_segs.
    (* [comment removed for export] *)
    assert (H1 : lo <= bv_unsigned sp - FP_DEPTH) by (unfold FP_DEPTH; lia).
    assert (H2 : alloc_ceiling <= lo) by exact CEIL.   (* [comment removed for export] *)
    assert (H3 : bv_unsigned sp <= 2^47) by lia.
    assert (H4 : AF + 33 <= RO_TOP) by (unfold RO_TOP; lia).
    assert (VL : fpsh_low AF 33 (aview A m)) by (split; [exact FPC| exact RNGA]).
    try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_ZSH); icall (fp_pre_u ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo AF 33 0xad928 FMT_REFUSED FMTB_REFUSED H1 H2 H3 H4
             U_fbytes U_fla pcm_fmt_refused
             t0 t1 t2 _ _ (Z_to_bv 64 67108864) a3 a4 a5 a6 a7 t3 t4 t5 t6 (aview A m) eq_refl eq_refl ST HF VL MI)
      by (first [mf_easm | reflexivity | lia]).
    lazymatch goal with H : stk rsegs ?mx lo _ |- _ => rename H into ST1;
      lazymatch goal with H2 : rw_cells rsegs mx (bv_unsigned sp + -112) _ |- _ => rename H2 into FPF1 end;
      lazymatch goal with H3 : mem_inv rsegs mx |- _ => rename H3 into MI1 end end.
    clear POST.
    (* [comment removed for export] *)
    assert (Q1 : lo <= bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -112)) - VFB_DEPTH) by (rewrite unsigned_lit by lia; unfold VFB_DEPTH; lia).
    assert (Q2 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -112)) <= 2^47) by (rewrite unsigned_lit by lia; lia).
    assert (F1 : mf_flags f0 = 5) by reflexivity.
    assert (F2 : mf_lock f0 = -1) by reflexivity.
    assert (F3 : mf_bufsize f0 = 0) by reflexivity.
    assert (F4 : 0 < mf_buf f0 < 2^63) by (subst f0; cbn_mfp; unfold stderr0; cbn [mf_buf]; unfold STDERR_BUFP; lia).
    assert (F5 : 0 <= mf_mode f0 < 2^32) by (subst f0; cbn_mfp; exact MOR).
    assert (F6 : FILE_LO <= 0xad928 /\ 0xad928 + 152 <= FILE_HI) by (unfold FILE_LO, FILE_HI; lia).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
    icall (vfu_pre FMT_REFUSED 33 U_hla pc1_refused towrite_ok
             (Z_to_bv 64 FP_VF_RET) (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp (Z_to_bv 64 AF) (Z_to_bv 64 0xad928) (Z_to_bv 64 (bv_unsigned sp + -48)) s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
             lo AF 0xad928 (bv_unsigned sp + -48) g f0
             Q1 Q2 H2 H4 F1 F2 F3 F5 F6
             _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mx eq_refl eq_refl eq_refl)
      by (first [ rewrite ?unsigned_lit by lia; mf_easm | split; mf_easm
                | subst f0; unfold file_at, file_cells; cbn_mfp; mf_easm | reflexivity | lia ]
          || match goal with |- ?G => idtac "UVFSIDE-FAIL" G end)
    end.
    lazymatch goal with H : stk rsegs ?mx lo _ |- _ => rename H into ST2;
      (first [ dand5 PC0 as APC2 AP2 JB2 JR2 VFR2 | destruct PC0 as (APC2 & AP2 & JB2 & JR2 & VFR2) ]); rename POST into FILE2; rename MI into MI2 end.
    pose proof (rw_CB_length _ _ _ _ _ JB2) as JBL.
    (* [comment removed for export] *)
    pose proof (proj2 (proj1 (proj2 (proj1 (rw_cells_app rsegs _ _ [_;_;_;_;_;_;_;_] _) FPF1)))) as VAB.
    cbn [cells_size csize Nat.add cells_bytes cbytes] in VAB. rewrite app_nil_r in VAB.
    match type of VAB with bytes_at _ _ ?ax _ => replace ax with (bv_unsigned sp + -48)%Z in VAB by (cbn; lia) end.
    rewrite <- u64s_6 in VAB.
    (* [comment removed for export] *)
    assert (R1 : lo <= bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -112 + -368)) - PC2_DEPTH) by (rewrite unsigned_lit by lia; unfold PC2_DEPTH; lia).
    assert (R2 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -112 + -368)) + 368 <= bv_unsigned sp + -48) by (rewrite unsigned_lit by lia; lia).
    assert (R3 : IMG_LO <= AF) by (unfold IMG_LO; lia).
    lazymatch type of FILE2 with file_at ?mx _ ?f1 =>
    assert (G1 : mf_flags f1 = 5) by reflexivity;
    assert (G2 : mf_wbase f1 = Z_to_bv 64 (mf_buf f1)) by reflexivity;
    assert (G3 : mf_wpos f1 = Z_to_bv 64 (mf_buf f1 + Z.of_nat (@length byte []))) by (cbn_mfp; cbn [length Z.of_nat]; rewrite Z.add_0_r; reflexivity);
    assert (G4 : mf_wend f1 = Z_to_bv 64 (mf_buf f1 + mf_bufsize f1)) by reflexivity;
    assert (G5 : 0 < mf_buf f1) by (cbn_mfp; lia);
    assert (G6 : mf_buf f1 + mf_bufsize f1 < 2^47) by (cbn_mfp; lia);
    assert (G7 : 0 <= mf_bufsize f1 < 2^31) by (cbn_mfp; lia);
    assert (G8 : mf_lbf f1 < 0) by (subst f0; cbn_mfp; unfold stderr0; cbn [mf_lbf]; lia);
    assert (G9 : -2^31 <= mf_lbf f1) by (subst f0; cbn_mfp; unfold stderr0; cbn [mf_lbf]; lia);
    assert (G10 : Z.of_nat (@length byte []) + 38 <= mf_bufsize f1) by (cbn_mfp; cbn [length Z.of_nat]; lia);
    lazymatch type of JB2 with rw_cells _ _ _ [CB 80 ?jb] =>
      assert (G11 : Z.of_nat (@length byte []) + Z.of_nat (length jb) = mf_bufsize f1) by (cbn_mfp; cbn [length Z.of_nat]; lia) end;
    assert (G12 : 0xad928 + 152 <= mf_buf f1 \/ mf_buf f1 + mf_bufsize f1 <= 0xad928) by (cbn_mfp; lia);
    assert (G13 : mf_buf f1 + mf_bufsize f1 <= lo \/ bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -112 + -368)) + 16 <= mf_buf f1) by (cbn_mfp; rewrite unsigned_lit by lia; lia);
    assert (G14 : (SBUF_LO <= mf_buf f1 /\ mf_buf f1 + mf_bufsize f1 <= SBUF_HI) \/ kHighMemBeg_z <= mf_buf f1) by (cbn_mfp; unfold kHighMemBeg_z; lia);
    assert (G15 : mf_buf f1 + mf_bufsize f1 <= bv_unsigned sp + -48) by (cbn_mfp; lia)
    end.
    pose proof (fok_sfF AF 33 (bv_unsigned sp - 464) 80 _ _ (bv_unsigned sp - 480 - PC2_DEPTH) (bv_unsigned sp - 480 + 96)
                  ltac:(lia) ltac:(lia) _ _ _ MU HW SF0) as SF1.
    assert (EA3 : Z_to_bv 64 (bv_unsigned sp + -112 + -272) = Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -112 + -368)) + 96)) by (f_equal; rewrite unsigned_lit by lia; lia).
    assert (EA4 : Z_to_bv 64 (bv_unsigned sp + -112 + -104) = Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -112 + -368)) + 264)) by (f_equal; rewrite unsigned_lit by lia; lia).
    try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_APC2); try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_JB2); lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
    lazymatch type of FILE2 with file_at _ _ ?f1 =>
    lazymatch type of JB2 with rw_cells _ _ _ [CB 80 ?jb] =>
    icall (pcu_all (Z_to_bv 64 VF_PC2_RET) (Z_to_bv 64 (bv_unsigned sp + -112 + -368)) gp tp (Z_to_bv 64 0xad928) (Z_to_bv 64 AF) (Z_to_bv 64 6325272) (Z_to_bv 64 1) (Z_to_bv 64 (mf_buf f0)) (Z_to_bv 64 5) s6 s7 s8 s9 s10 s11 F fc
             lo AF 0xad928 (bv_unsigned sp + -48) g f1 [] jb [a3; a4; a5; a6; a7]
             (sh alloc_ceiling) (Z.to_nat ((2^47 - alloc_ceiling) / 8))
             fwritex_fit_ok R1 H2 R2 R3 H4 G1 G2 G3 G4 G5 G6 G7 G8 G9 G10 G11 F6 G12 G13 G14 G15
             _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mx eq_refl eq_refl eq_refl EA3 EA4)
      by (first [ rewrite ?unsigned_lit by lia; mf_easm | split; mf_easm
                | apply bytes_at_nil; cbn_mfp; lia
                | lazymatch goal with |- rw_cells _ _ _ [CB (length ?jb') _] => cbn_mfp; cbn [length Z.of_nat]; rewrite ?Z.add_0_r;
                    eapply rw_cells_recast_pf; [exact JB2| cbn; split; [reflexivity| exact I] | reflexivity] end
                | rewrite ?unsigned_lit by lia; f_equal; lia
                | lazymatch goal with |- sfF _ _ _ _ _ _ _ _ _ => cbn_mfp; rewrite ?unsigned_lit by lia;
                    replace (bv_unsigned sp + -112 + -368 - PC2_DEPTH) with (bv_unsigned sp - 480 - PC2_DEPTH) by lia;
                    replace (bv_unsigned sp + -112 + -368 + 96) with (bv_unsigned sp - 480 + 96) by lia;
                    replace (bv_unsigned sp + -112 + -352) with (bv_unsigned sp - 464) by lia; exact SF1 end
                | reflexivity | lia ]
          || match goal with |- ?G => idtac "PCUSIDE-FAIL" G end)
    end end end.
    clear SF1.
    lazymatch goal with H : stk rsegs ?mx lo _ |- _ => rename H into ST3; rename PC0 into FILE3; rename PC1 into BUF3; rename PC2 into RST3;
      rename PC3 into APC3; rename PC4 into SSP3; rename POST into SF3; rename MI into MI3 end.
    cbn [app] in BUF3.
    replace (bv_unsigned sp + -112 + -352 + Z.of_nat (@length byte []))%Z with (bv_unsigned sp + -112 + -352)%Z in * by (cbn [length Z.of_nat]; lia).
    (* [comment removed for export] *)
    sp_nest (bv_unsigned sp + -112) (-368).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
    lazymatch goal with FI : file_at mx 710952 ?fx |- _ =>
    pcall (vfu_mid FMT_REFUSED (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp s6 s7 s8 s9 s10 s11 F fc lo AF 0xad928 f0 F4
             _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mx fx)
      by (first [ rewrite ?unsigned_lit by lia; mf_easm | cbn_mfp; reflexivity | subst f0; cbn_mfp; unfold stderr0; cbn; reflexivity ]
          || match goal with |- ?G => idtac "UVMID-FAIL" G end)
    end end.
    lazymatch goal with H : stk rsegs ?mx lo _ |- _ => rename H into ST8; lazymatch goal with FI : file_at mx 710952 _ |- _ => rename FI into FILE8 end;
      lazymatch goal with Bq : bytes_at rsegs mx (bv_unsigned sp + -112 + -352) _ |- _ => rename Bq into BUF8 end;
      lazymatch goal with Mq : mem_inv rsegs mx |- _ => rename Mq into MI8 end end.
    (* [comment removed for export] *)
    astopx AINV MU WM CF. rename m0 into m1. rename md0 into md1. rename AINV0 into AINV1.
    pose proof (as_minv LPA A m1 md1 AINV1) as [_ HH1].
    (first [ pose proof ((sbm_io md md1 SBM)) as dR_17; dand3 dR_17 as FS1 FDS1 _ | pose proof (sbm_io md md1 SBM) as (FS1 & FDS1 & _) ]).
    rewrite U_msg. rewrite <- (app_nil_r U_MSG).
    lazymatch type of FILE8 with file_at _ _ ?f8 =>
    eapply (stdio_write_ok _ _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 md1 A
              0xad928 f8 U_MSG [] 0 _ lo K AINV1 MI8) end.
    all: lazymatch goal with
         | |- forall m' md', ainv _ _ _ -> _ => idtac
         | |- ?G => first [ reflexivity
                          | rewrite ?unsigned_lit by lia; mf_easm
                          | right; subst f0; cbn_mfp; unfold stderr0; cbn [mf_fd]; reflexivity
                          | unfold img_client; cbn [cl_rw_lo cl_image_hi LPA]; split; [cbn; lia| split; [cbn; lia| intros aa Ha; cbn [cl_static cl_shared LPA]; unfold pa_static, pa_shared; lia]]
                          | subst f0; cbn_mfp; unfold stderr0; cbn [mf_fd]; rewrite FDS1; exact FDL
                          | cbn_mfp; rewrite ?U_len; cbn [length Z.of_nat]; first [reflexivity | f_equal; lia | lia]
                          | cbn_mfp; bytes_from_hyp
                          | apply bytes_at_nil; lia
                          | eexists; mf_easm
                          | exact HK
                          | unfold STDIO_WRITE_STACK; rewrite ?unsigned_lit by lia; cbn_mfp; rewrite ?U_len; cbn [length Z.of_nat]; lia ]
                    || idtac "UW3-FAIL" G
         end.
    intros m2 md2 AINV2 IO2 FILE9 ms' PO2.
    destruct_exs PO2. destruct PO2 as [E [MU2 [WM2 [MI9 ST9]]]]. subst ms'.
    unfold STDIO_WRITE_STACK in MU2, ST9. rewrite ?unsigned_lit in MU2 by lia. rewrite ?unsigned_lit in ST9 by lia.
    cbn_mfp_in FILE9.
    transport_after_call rsegs (aview A m1) (aview A m2) MU2 WM2. clear MU2 WM2 MI8.
    (first [ dand3 IO2 as FS2 FDS2 _ | destruct IO2 as (FS2 & FDS2 & _) ]).
    (* [comment removed for export] *)
    pose proof (munch_refl [(bv_unsigned sp - 8192, bv_unsigned sp); (0xad928, 0xad928 + 152)] (aview A m2)) as MUe.
    pose proof (wmono_refl rsegs (aview A m2)) as WMe.
    assert (CFe : client_fpx (L:=LPA) A (aview A m2) [(bv_unsigned sp - 8192, bv_unsigned sp); (0xad928, 0xad928 + 152)]).
    { cbn. split. { left. split; [| exact I]. left. split; [lia|]. split; [lia|].
        lazymatch goal with H : wr_at rsegs (aview A m2) (bv_unsigned sp - 8192) 8192 |- _ =>
          replace (bv_unsigned sp - (bv_unsigned sp - 8192)) with 8192 by lia; eapply (wr_at_mapped LPA); [exact H| apply (off_image_stack LPA); lia] end. }
      split; [| exact I]. right. split; [cbn; lia|]. split; [cbn; lia|]. intros aa Ha. cbn [cl_static cl_shared LPA]. unfold pa_static, pa_shared. lia. }
    ago AINV2. fold_cl_segs. fix_retpc.
    sp_nest (bv_unsigned sp + -112) (-368).
    try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_AP2); try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_APC3); try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_BUF8); try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_JR2); try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_RST3); try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_VFR2); lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
    lazymatch goal with FI : file_at mx 710952 ?f9 |- _ =>
    lazymatch goal with Rq : rw_cells rsegs mx _ [CB _ (skipn ?k ?jb)] |- _ =>
    lazymatch goal with JRq : rw_cells rsegs mx (bv_unsigned sp + -112 + -272) [CB 168 ?jr] |- _ =>
    lazymatch goal with Bq : bytes_at rsegs mx (bv_unsigned sp + -112 + -352) ?pd |- _ =>
    icall (vfu_post FMT_REFUSED (Z_to_bv 64 FP_VF_RET) (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp (Z_to_bv 64 AF) (Z_to_bv 64 0xad928) (Z_to_bv 64 (bv_unsigned sp + -48)) s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
             lo 0xad928 (bv_unsigned sp + -48) g f0 Q1 H2 F6
             _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mx f9 (pd ++ skipn k jb) jr (bv_unsigned sp + -112 + -352) _)
      by (first [ rewrite ?unsigned_lit by lia; mf_easm | split; mf_easm | cbn_mfp; reflexivity | cbn_mfp; lia
                | lazymatch goal with |- rw_cells _ _ _ [CB _ (_ ++ _)] => rewrite ?unsigned_lit by lia;
                    eapply rwc_eq;
                    [ eapply rw_CB_of_parts; [ exact WRB | bytes_from_hyp | rw_CB_from_hyp
                                             | lazymatch goal with H : rw_cells rsegs _ _ [CB _ (skipn k jb)] |- _ => pose proof (rw_CB_length _ _ _ _ _ H) end;
                                               rewrite ?length_app, ?length_skipn in *; cbn [length] in *; lia ]
                    | lia ] end ]
          || match goal with |- ?G => idtac "UVPOST-FAIL" G end)
    end end end end end.
    lazymatch goal with H : stk rsegs ?mx lo (bv_unsigned sp + -112) |- _ => rename H into STy;
      lazymatch goal with FI : file_at mx 710952 _ |- _ => rename FI into FILEy end;
      lazymatch goal with Mq : mem_inv rsegs mx |- _ => rename Mq into MIy end end.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
    pcall (fp_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo FMTB_REFUSED H1
             _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mx _ _ _ _ _ _ _)
      by (first [ rewrite ?unsigned_lit by lia; mf_easm ] || match goal with |- ?G => idtac "UFPOST-FAIL" G end)
    end.
    lazymatch goal with H : stk rsegs ?mx lo (bv_unsigned sp) |- _ => rename H into STz end.
    (* [comment removed for export] *)
    astopx AINV2 MUe WMe CFe. rename m0 into mz. rename md0 into mdz. rename AINV0 into AINVz.
    pose proof (as_minv LPA A mz mdz AINVz) as [_ HHz].
    (first [ pose proof ((sbm_io _ mdz SBM0)) as dR_19; dand3 dR_19 as FSz FDSz _ | pose proof (sbm_io _ mdz SBM0) as (FSz & FDSz & _) ]).
    lazymatch type of FILEy with file_at _ _ ?fz => eapply (HKONT mz mdz fz _ AINVz) end.
    { split; [| split; [| exact HHz]]; congruence. }
    { lazymatch goal with |- stderr_ok ?fz => eexists w0, _; split; [| left; reflexivity]; subst f0; norm_mf_eq; reflexivity end. }
    { exact FILEy. }
    hot_eexists_all. split; [reflexivity|].
    split. { first [ exact MU | eapply munch_trans; [exact MU|]; eapply munch_weaken; [| exact MUe]; unfold sub_fp; cbn [outside]; intros; lia ]. }
    split. { first [ exact WM | eapply wmono_trans; [exact WM| exact WMe] ]. }
    split; [exact MIy| exact STz].
  Qed.
  End SU.

  Theorem fprintf_diag_ok : fprintf_diag_stmt.
  Proof.
    unfold fprintf_diag_stmt. intros until K. cbv zeta.
    intros AINV MI TP A0 A1 DM N17 ZSH FILE SOK SBUFPx FDL CANx GOT ST LO CEIL SP16 SPHI HK HKONT.
    destruct d.
    - (first [ dand8 DM as A2 SB NIN PALO PAHI SL16 SPP PADc | destruct DM as (A2 & SB & NIN & PALO & PAHI & SL16 & SPP & PADc) ]). rewrite (s3_msg DF_usage arg I).
      eapply (fprintf_diag_s_go DF_usage); first [exact I | mf_easm].
    - (first [ dand8 DM as A2 SB NIN PALO PAHI SL16 SPP PADc | destruct DM as (A2 & SB & NIN & PALO & PAHI & SL16 & SPP & PADc) ]). rewrite (s3_msg DF_cannot_open arg I).
      eapply (fprintf_diag_s_go DF_cannot_open); first [exact I | mf_easm].
    - (first [ dand8 DM as A2 SB NIN PALO PAHI SL16 SPP PADc | destruct DM as (A2 & SB & NIN & PALO & PAHI & SL16 & SPP & PADc) ]). rewrite (s3_msg DF_read_error arg I).
      eapply (fprintf_diag_s_go DF_read_error); first [exact I | mf_easm].
    - destruct DM as [A2 ->]. cbn [diag_msg].
      eapply fprintf_diag_u_go; mf_easm.
  Qed.

End Leaves.
