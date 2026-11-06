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
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CallLit CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require ImgA RA_seql.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require RA_sjs3.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require RA_sjs3 PF_low PF_pc1.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf.ImgA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf.RA_seql OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf.RA_sjs3.RA_pdfk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf.RA_sjs3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf.PF_low OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf.PF_pc1.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcp2qs AIcp0e6.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc AIcp7wm.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpkua.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpkua AIcpya4 AIcp3q7.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpwpz.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpwpz AIcpw0i.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpq85.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpq85.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc.AIcpdmn OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcp2qs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcp0e6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc.AIcpxbj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc.AIcp6d9 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcp7wm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpkua.AIcpilj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpkua OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpya4 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcp3q7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpwpz.AIcpdm8 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpwpz OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpw0i OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpq85.AIcpa3z OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpq85.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import ExN.   (* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac hot_qset := lazymatch goal with |- evt _ ?Q _ => lazymatch Q with (fun _ => _) => set (hotQ := Q) | _ => idtac end | |- _ => idtac end.
Ltac hot_qend := lazymatch goal with |- evt _ ?Q _ => first [ is_var Q; subst Q | idtac ] | |- ?Q _ => first [ is_var Q; subst Q; cbv beta | idtac ] | |- _ => idtac end.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd Require Import DA_Eg3i DA_Cells DA_Ldix.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import PF_file PF_pc2d.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Storrsf.
Import ListNotations.
Open Scope bv_scope.

Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac lia ::= lia3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Ltac icpt_consts_in H ::= unfold MEMSET_ICPT_STACK, FWRITEX_STACK, STRNLEN_ICPT_STACK, fwritex_fit_post, strnlen_icpt_post in H; cbn [length Z.of_nat Nat.sub skipn mf_set_w mf_set_write_lbf mf_flags mf_rpos mf_rend mf_close mf_wend mf_wpos mf_mbz1 mf_wbase mf_read mf_write mf_seek mf_buf mf_bufsize mf_prev mf_next mf_fd mf_pipepid mf_lockcount mf_mode mf_lock mf_lbf mf_pad148] in H; rewrite ?Z.add_0_r in H.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require JunkName.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.split_for_access H segs m A cs kn n ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.JunkName.split_for_access_jn H segs m A cs kn n.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaSec.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_sec.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor5a9.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor5a9.sd_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor5a9.sd_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor5a9.sd_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor5a9.sd_transport_after_call segs m m' MU WM.
(* [comment removed for export] *)
From Ltac2 Require Ltac2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require KDrop.
Ltac hot_kdrop := ltac2:(Ltac2.Control.enter (fun () => OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.kdrop_marked ())).
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= hot_kdrop; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor5a9.sd_transport_after_call segs m m' MU WM.
(* [comment removed for export] *)
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Diet8ul.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Diet8ul.dlia_sec.
(* [comment removed for export] *)
(* [comment removed for export] *) From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor0fe.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor0fe.sb_mem_after_store_sfdx.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require DietDL3.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.sec_local := Ltac2.Init.true.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.sep_idents := OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.sep_idents_hide.
(* [comment removed for export] *)
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.sep_idents := fun () => [@apart; @sf_hide; @dl_sep].   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition sfS (A la B N : Z) (SB : Z) (K : nat) (zlo zhi P ln : Z) (m : word -> option byte) : Prop :=
  sfF A la B N SB K zlo zhi m /\ strnlen_icpt_cells m /\ range_ok m P ln.
Lemma fok_strnlen_icpt_cells : fokP strnlen_icpt_cells.
Proof.
  unfold strnlen_icpt_cells, asan_inited_cell. do 5 (apply fokP_and; [apply fok_ro_cells; far_cells|]). apply fok_map_cells.
Qed.
Lemma fok_sfS : forall A la B N SB K zlo zhi P ln, (0 <= la)%Z -> (0 <= N)%Z -> (0 <= ln)%Z -> fokP (sfS A la B N SB K zlo zhi P ln).
Proof.
  intros. apply fokP_and; [apply fok_sfF; lia| apply fokP_and; [apply fok_strnlen_icpt_cells| apply fok_range_ok; lia]].
Qed.
Local Ltac fok_lemma P ::= lazymatch P with
  | sfS ?A ?la ?B ?N ?SB ?K ?zlo ?zhi ?P ?ln => constr:(fok_sfS A la B N SB K zlo zhi P ln ltac:(lia) ltac:(lia) ltac:(lia))
  | sfF ?A ?la ?B ?N ?SB ?K ?zlo ?zhi => constr:(fok_sfF A la B N SB K zlo zhi ltac:(lia) ltac:(lia))
  | _ => fok_lemma_base P end.
Local Ltac solve_wfok ::= cbn [wfok]; rewrite ?length_app, ?length_skipn;
  cbn [length Z.of_nat mf_set_w mf_buf mf_bufsize]; unfold kHighMemBeg_z, FILE_LO, FILE_HI, SBUF_LO, SBUF_HI in *; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try exact I; lia.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= refok_store_hook m a bs n Hn Ha Hl.
Local Ltac transport_call_extra segs W m m' MU WM ::= refok_all W m m' MU.
Local Ltac icpt_relow W m m' MU ::= refok_all W m m' MU.

(* [comment removed for export] *)
Ltac fwx_rangeS :=
  rewrite ?unsigned_lit by lia; cbn [length Z.of_nat];
  lazymatch goal with SFq : sfS _ _ _ _ _ _ _ _ _ _ ?mm |- range_ok ?mm ?a ?n =>
    first [ eapply (sfF_buf_range _ _ _ _ _ _ _ _ _ _ _ (proj1 SFq)); lia
          | eapply (sfF_fmt_range _ _ _ _ _ _ _ _ _ _ _ (proj1 SFq)); lia
          | eapply (sfF_stack_range _ _ _ _ _ _ _ _ _ _ _ (proj1 SFq)); lia
          | eapply range_ok_sub; [exact (proj2 (proj2 SFq))| lia| lia| lia] ] end.
Ltac fwx_sideS FL5 :=
  idtac; cbn [mf_set_w mf_set_write_lbf mf_flags mf_rpos mf_rend mf_close mf_wend mf_wpos mf_mbz1 mf_wbase mf_read mf_write mf_seek mf_buf mf_bufsize mf_prev mf_next mf_fd mf_pipepid mf_lockcount mf_mode mf_lock mf_lbf mf_pad148];
  lazymatch goal with
  | |- file_at ?mx ?fa _ => apply file_p5_at; [exact FL5 | match goal with H : rw_cells rsegs mx fa _ |- _ => exact H end]
  | |- bytes_at _ _ _ [] => apply bytes_at_nil; lia
  | |- bytes_at _ _ _ _ => rewrite ?unsigned_lit by lia; first [eassumption | eapply bytes_at_eqa; [eassumption | rewrite ?length_app; cbn [length]; lia]]
  | |- rw_cells _ _ _ _ => rewrite ?unsigned_lit by lia; first [eassumption | rewrite ?length_app, ?length_skipn; cbn [length Z.of_nat]; eapply rwc_eq; [eassumption | cbn [length]; rewrite ?length_app; cbn [length]; lia]]
  | |- stk _ _ _ _ => rewrite ?unsigned_lit by lia; eassumption
  | |- mem_inv _ _ => eassumption
  | |- memcpy_icpt_cells _ => lazymatch goal with SFq : sfS _ _ _ _ _ _ _ _ _ _ _ |- _ => exact (proj1 (proj1 SFq)) end
  | |- @eq _ _ _ => rewrite ?unsigned_lit by lia; first [reflexivity | assumption | cbn; f_equal; lia | cbn; rewrite ?length_app, ?length_skipn; cbn; first [f_equal; lia | lia]]
  | |- (_ \/ ~ In _ _)%type => left; cbn; lia
  | |- (_ = 0%Z \/ _)%type => first [left; reflexivity | left; cbn; lia | right; split; fwx_rangeS]
  | |- _ \/ _ => rewrite ?unsigned_lit by lia; cbn [length Z.of_nat]; rewrite ?Z.add_0_r, ?length_app; cbn [length Z.of_nat]; lia
  | |- _ => rewrite ?unsigned_lit by lia; unfold FWRITEX_STACK; cbn [length Z.of_nat]; rewrite ?length_app, ?length_skipn; cbn [length Z.of_nat]; lia
  end || match goal with |- ?G => idtac "FWXSIDE-FAIL:" G end.

(* [comment removed for export] *)
Definition s3_ok (d : diag_fmt) : Prop := match d with DF_refused => False | _ => True end.
Definition s3_fmt (d : diag_fmt) : list cell :=
  match d with DF_usage => FMT_USAGE | DF_cannot_open => FMT_COPEN | DF_read_error => FMT_RERR | DF_refused => FMT_USAGE end.
Definition zb8 (l : list Z) : list byte := map (fun z => Z_to_bv 8 z) l.
Definition L1_USAGE : list byte := Eval cbv [zb8 map] in zb8 [117; 115; 97; 103; 101; 58; 32]%Z.
Definition L1_COPEN : list byte := Eval cbv [zb8 map] in zb8 [99; 108; 105; 58; 32; 99; 97; 110; 110; 111; 116; 32; 111; 112; 101; 110; 32]%Z.
Definition L1_RERR : list byte := Eval cbv [zb8 map] in zb8 [99; 108; 105; 58; 32; 114; 101; 97; 100; 32; 101; 114; 114; 111; 114; 32; 111; 110; 32]%Z.
Definition L2_USAGE : list byte := Eval cbv [zb8 map] in zb8 [32; 73; 78; 80; 85; 84; 10]%Z.
Definition L2_NL : list byte := [Z_to_bv 8 10].
Definition s3_L1 (d : diag_fmt) : list byte :=
  match d with DF_cannot_open => L1_COPEN | DF_read_error => L1_RERR | _ => L1_USAGE end.
Definition s3_L2 (d : diag_fmt) : list byte :=
  match d with DF_usage | DF_refused => L2_USAGE | _ => L2_NL end.
Definition s3_la (d : diag_fmt) : Z := match d with DF_cannot_open => 21 | DF_read_error => 23 | _ => 17 end.
Lemma s3_fmt_bytes : forall d, cells_bytes (s3_fmt d) = s3_L1 d ++ [Z_to_bv 8 37; Z_to_bv 8 115] ++ s3_L2 d ++ [Z_to_bv 8 0].
Proof. intros []; reflexivity. Qed.
Lemma s3_la_size : forall d, Z.of_nat (cells_size (s3_fmt d)) = s3_la d.
Proof. intros []; reflexivity. Qed.

(* [comment removed for export] *)
Lemma nul_read : forall m P (str slack : list byte),
  bytes_at rsegs m P (str ++ Z_to_bv 8 0 :: slack) ->
  ov_read_bytes rsegs m (Z_to_bv 64 (P + Z.of_nat (length str))) 1 = Some [Z_to_bv 8 0].
Proof.
  intros m P str slack H.
  pose proof (bytes_at_ov_read rsegs m P _ (length str) 1 H ltac:(rewrite length_app; cbn; lia)) as R.
  unfold wa in R. rewrite skipn_app, skipn_all2, Nat.sub_diag in R by lia. exact R.
Qed.

(* [comment removed for export] *)
Lemma memchr_len_cstr : forall nn (str slack : list byte),
  ~ In (Z_to_bv 8 0) str -> (Z.of_nat (length str) < nn)%Z ->
  memchr_len 0 nn (str ++ Z_to_bv 8 0 :: slack) = (Z.of_nat (length str) + 1)%Z.
Proof.
  intros nn str slack NIN Hn. unfold memchr_len. rewrite (find_byte_cstr 0 nn str slack NIN Hn). reflexivity.
Qed.

(* [comment removed for export] *)
Definition padP (P n ls : Z) : Prop := ((- (P + n + 1)) mod 8 <= ls)%Z.

Definition ARG_RET : Z := 0x9f718.   (* [comment removed for export] *)
Definition PFX_A : Z := 0x10b85.      (* [comment removed for export] *)

Section PC2S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (d : diag_fmt) (lo A Fa VA P : Z) (canary : word) (f : mfile) (pend rest str slack : list byte) (vrest : list word) (ZSB : Z) (ZK : nat).
  Hypothesis FWXC : fwritex_fit_stmt.
  Hypothesis D3 : s3_ok d.
  #[local] Notation q := (bv_unsigned sp).
  #[local] Notation B := (mf_buf f).
  #[local] Notation N := (mf_bufsize f).
  #[local] Notation wp := (mf_buf f + Z.of_nat (length pend))%Z.
  #[local] Notation l1 := (Z.of_nat (length (s3_L1 d))).
  #[local] Notation l2 := (Z.of_nat (length (s3_L2 d))).
  #[local] Notation n := (Z.of_nat (length str)).
  (* [comment removed for export] *)
  Hypothesis LO : (lo <= q - PC2_DEPTH)%Z.
  Hypothesis GT : (alloc_ceiling <= lo)%Z.   (* [comment removed for export] *)
  Hypothesis VLO : (q + 368 <= VA)%Z.
  Hypothesis VHI : (VA + 48 <= 2^63)%Z.
  Hypothesis ARL : (IMG_LO <= A)%Z.
  Hypothesis ART : (A + s3_la d <= RO_TOP)%Z.
  Hypothesis FL5 : mf_flags f = 5%Z.
  Hypothesis FWB : mf_wbase f = Z_to_bv 64 B.
  Hypothesis FWP : mf_wpos f = Z_to_bv 64 wp.
  Hypothesis FWE : mf_wend f = Z_to_bv 64 (B + N).
  Hypothesis B0 : (0 < B)%Z.
  Hypothesis BHI : (B + N < 2^47)%Z.
  Hypothesis NR : (0 <= N < 2^31)%Z.
  Hypothesis LBF : (mf_lbf f < 0)%Z.
  Hypothesis LBR : (-2^31 <= mf_lbf f)%Z.
  Hypothesis ROOM : (Z.of_nat (length pend) + l1 <= N)%Z.
  Hypothesis PR : (Z.of_nat (length pend) + Z.of_nat (length rest) = N)%Z.
  Hypothesis FAR : (FILE_LO <= Fa /\ Fa + 152 <= FILE_HI)%Z.
  Hypothesis FB1 : (Fa + 152 <= B \/ B + N <= Fa)%Z.
  Hypothesis FB2 : (B + N <= lo \/ q + 16 <= B)%Z.
  Hypothesis FB3 : ((SBUF_LO <= B /\ B + N <= SBUF_HI) \/ kHighMemBeg_z <= B)%Z.
  Hypothesis FBV : (B + N <= VA)%Z.
  (* [comment removed for export] *)
  Hypothesis P0 : (q + 368 <= P)%Z.
  Hypothesis PHI : (P + n + 1 + Z.of_nat (length slack) < 2^47)%Z.
  Hypothesis NIN : ~ In (Z_to_bv 8 0) str.
  Hypothesis PAD : padP P n (Z.of_nat (length slack)).
  Hypothesis N17 : (n <= 2^17)%Z.
  Hypothesis PB2 : (B + N <= P)%Z.

  Notation FRAME1 m1 j40 := (rw_cells rsegs m1 (q + -544) (CB 40 j40 :: pc_lits sp)).
  Notation FRAMEA m1 ja1 ja2 := (rw_cells rsegs m1 (q + -432) [CB 8 ja1; CB 8 ja2]).
  Notation FRAME2 m1 j304 := (rw_cells rsegs m1 (q + -416) (CB 304 j304 :: pc_saved ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 canary)).
  Notation SFS m1 := (sfS A (s3_la d) B N ZSB ZK (q - PC2_DEPTH) (q + 96) P (n + 1) m1).

  (* [comment removed for export] *)
  Definition pcs_mid1 (m : word -> option byte) : machine_state -> Prop :=
    fun ms => exists (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (j40 ja2 j304 : list byte) (m' : word -> option byte),
      ms = MS (mkR (Z_to_bv 64 ARG_RET) (Z_to_bv 64 (q + -544)) gp tp t0 t1 t2 (Z_to_bv 64 37) (Z_to_bv 64 INT_MAX)
                   (Z_to_bv 64 P) (Z_to_bv 64 n) (Z_to_bv 64 Fa) a3 a4 a5 a6 a7
                   (Z_to_bv 64 0) (Z_to_bv 64 l1) (Z_to_bv 64 Fa) (Z_to_bv 64 (A + l1 + 2)) (Z_to_bv 64 0) (Z_to_bv 64 P)
                   (Z_to_bv 64 0) (Z_to_bv 64 n) (Z_to_bv 64 n) (Z_to_bv 64 n) t3 t4 t5 t6)
              F (Z_to_bv 64 FWRITEX_ENTRY) fc None m' (seg_rom rsegs)
      /\ munch [(q - PC2_DEPTH, q + 8); (Fa, Fa + 152); (wp, wp + l1)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
      /\ stk rsegs m' lo (q + -544)
      /\ FRAME1 m' j40 /\ rw_cells rsegs m' (q + -432) [C8 (Z_to_bv 64 P); CB 8 ja2] /\ FRAME2 m' j304
      /\ file_at m' Fa (mf_set_w f (Z_to_bv 64 (wp + l1)) (Z_to_bv 64 B) (Z_to_bv 64 (B + N)))
      /\ bytes_at rsegs m' B (pend ++ s3_L1 d)
      /\ rw_cells rsegs m' (wp + l1) [CB (length rest - length (s3_L1 d))%nat (skipn (length (s3_L1 d)) rest)]
      /\ rw_cells rsegs m' q [C8 (Z_to_bv 64 (VA + 8))]
      /\ bytes_at rsegs m' P (str ++ Z_to_bv 8 0 :: slack)
      /\ ssp_cells m' canary /\ SFS m'.

  (* [comment removed for export] *)
  Lemma ro_cells_app_l : forall m0 A0 cs1 cs2,
    ro_cells rsegs m0 A0 (cs1 ++ cs2) -> ro_cells rsegs m0 (A0 + Z.of_nat (cells_size cs1)) cs2.
  Proof.
    intros m0 A0 cs1 cs2. unfold ro_cells, cells_at. rewrite cells_wf_app, cells_bytes_app, bytes_at_app.
    intros ((W1 & W2) & (B1 & B2)). rewrite (cells_bytes_length cs1 W1) in B2. split; assumption.
  Qed.
  Lemma ro_cells_prefix2 : forall m0 A0 c1 c2 cs, ro_cells rsegs m0 A0 (c1 :: c2 :: cs) -> ro_cells rsegs m0 A0 [c1; c2].
  Proof.
    intros m0 A0 c1 c2 cs. change (c1 :: c2 :: cs) with ([c1; c2] ++ cs). unfold ro_cells, cells_at. rewrite cells_wf_app, cells_bytes_app, bytes_at_app.
    intros ((W1 & W2) & (B1 & B2)). split; assumption.
  Qed.
  Lemma s3_fmt_cells : forall d0, s3_fmt d0 = map C1 (s3_L1 d0) ++ C1 (Z_to_bv 8 37) :: C1 (Z_to_bv 8 115) :: map C1 (s3_L2 d0 ++ [Z_to_bv 8 0]).
  Proof. intros []; reflexivity. Qed.
  Lemma s3_la_split : forall d0, (Z.of_nat (length (s3_L1 d0)) + 3 + Z.of_nat (length (s3_L2 d0)) = s3_la d0)%Z.
  Proof. intros []; reflexivity. Qed.
  Lemma cells_size_map_C1 : forall l : list byte, cells_size (map C1 l) = length l.
  Proof. induction l as [|b l IH]; [reflexivity|]. cbn [map cells_size csize length]. rewrite IH. reflexivity. Qed.

  Definition pcs_cut (m : word -> option byte) : machine_state -> Prop :=
    fun ms => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (j40 ja1 ja2 j304 : list byte) (m' : word -> option byte),
      ms = MS (mkR (Z_to_bv 64 FWX5_RET) (Z_to_bv 64 (q + -544)) gp tp t0 t1 t2 (Z_to_bv 64 37) (Z_to_bv 64 INT_MAX)
                   (Z_to_bv 64 l1) a1 a2 a3 a4 a5 a6 a7
                   (Z_to_bv 64 INT_MAX) (Z_to_bv 64 0) (Z_to_bv 64 Fa) (Z_to_bv 64 (A + l1)) (Z_to_bv 64 l1) (Z_to_bv 64 A)
                   s8 s9 (Z_to_bv 64 l1) s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x9ec60) fc None m' (seg_rom rsegs)
      /\ munch [(q - PC2_DEPTH, q + 8); (Fa, Fa + 152); (wp, wp + l1)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
      /\ stk rsegs m' lo (q + -544)
      /\ ro_cells rsegs m' (A + l1) [C1 (Z_to_bv 8 37); C1 (Z_to_bv 8 115)] /\ ssp_cells m' canary
      /\ FRAME1 m' j40 /\ FRAMEA m' ja1 ja2 /\ FRAME2 m' j304
      /\ file_at m' Fa (mf_set_w f (Z_to_bv 64 (wp + l1)) (Z_to_bv 64 B) (Z_to_bv 64 (B + N)))
      /\ bytes_at rsegs m' B (pend ++ s3_L1 d)
      /\ rw_cells rsegs m' (wp + l1) [CB (length rest - length (s3_L1 d))%nat (skipn (length (s3_L1 d)) rest)]
      /\ rw_cells rsegs m' q [C8 (Z_to_bv 64 VA)]
      /\ bytes_at rsegs m' VA (u64s (Z_to_bv 64 P :: vrest))
      /\ bytes_at rsegs m' P (str ++ Z_to_bv 8 0 :: slack)
      /\ SFS m'.

  #[using="PB2 N17 PAD NIN PHI P0 FBV FB3 FB2 FB1 FAR PR ROOM LBR LBF NR BHI B0 FWE FWP FWB FL5 ART ARL VLO GT LO D3 FWXC Clg"] Lemma pcs_head_a : forall t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (m : word -> option byte),
    a0 = Z_to_bv 64 Fa -> a1 = Z_to_bv 64 A -> a2 = sp -> a3 = Z_to_bv 64 (q + 96) -> a4 = Z_to_bv 64 (q + 264) ->
    stk rsegs m lo q -> ro_cells rsegs m A (s3_fmt d) -> ssp_cells m canary ->
    file_at m Fa f -> bytes_at rsegs m B pend -> rw_cells rsegs m wp [CB (length rest) rest] ->
    rw_cells rsegs m q [C8 (Z_to_bv 64 VA)] -> va_area m VA (Z_to_bv 64 P :: vrest) ->
    bytes_at rsegs m P (str ++ Z_to_bv 8 0 :: slack) ->
    mem_inv rsegs m -> SFS m ->
    evt rsegs (pcs_cut m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PRINTF_CORE) fc None m (seg_rom rsegs)).
  Proof.
    intros until m. intros -> -> -> -> -> ST HF [SSP1 SSP2] FILE BUF RST APC VAA SB MI SF.
    pose proof alloc_ceiling_val as CV. unfold pcs_cut.
    unfold RA_seql.GOT_SSP, RA_seql.SSP_GUARD, DA_Eg3i.SSP_GUARD, GLOBALS_TOP, RO_TOP, PC2_DEPTH, PRINTF_CORE, IMG_LO, IMG_HI, FILE_LO, FILE_HI, SBUF_LO, SBUF_HI, kHighMemBeg_z in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (ro_cells_bound _ _ _ _ HF) as AB. rewrite s3_la_size in AB.
    pose proof (bytes_at_bound _ _ _ _ BUF) as BB. pose proof (rw_CB_length _ _ _ _ _ RST) as RL.
    pose proof (bytes_at_bound _ _ _ _ SB) as PB. rewrite length_app in PB. cbn [length] in PB.
    assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(bv_unsigned sp - 4928, bv_unsigned sp + 8); (Fa, Fa + 152); (mf_buf f + Z.of_nat (length pend), mf_buf f + Z.of_nat (length pend) + l1)]%Z m) as MU.
    pose proof (wmono_refl rsegs m) as WM.
    unfold va_area in VAA.
    apply (file_at_p5 _ _ _ FL5) in FILE. unfold pfile5, file_cells in FILE. cbn [tl] in FILE.
    pose proof FWXC as FWX. unfold fwritex_fit_stmt in FWX. cbv zeta in FWX.
    assert (Q47 : (bv_unsigned sp + 112 <= 2^47)%Z) by (destruct SF as ((_ & _ & _ & _ & _ & (_ & _ & _ & _ & B5 & _) & _) & _); lia).
    (* [comment removed for export] *)
    pose proof (s3_la_size d) as LAS.
    assert (HFP : ro_cells rsegs m (A + l1) [C1 (Z_to_bv 8 37); C1 (Z_to_bv 8 115)]).
    { pose proof HF as HFx. rewrite s3_fmt_cells in HFx. apply ro_cells_app_l in HFx. rewrite cells_size_map_C1 in HFx. exact (ro_cells_prefix2 _ _ _ _ _ HFx). }
    rewrite <- (Z_to_bv_bv_unsigned sp) at 1.
    fwx_leqs.
    carve_frame 544%nat ST.
    hot_qset.
    do 43 zs; name_junk FR.
    (* [comment removed for export] *)
    apply (rw_cells_split_CB rsegs _ _ [_;_;_;_;_;_;_;_;_;_] 320 _ _ [8; 8; 304]%nat) in FR; [|reflexivity];
         cbn [mk_CB_cells app] in FR;
         apply (proj1 (rw_cells_app rsegs _ _ [_;_;_;_;_;_;_;_;_;_] _)) in FR; destruct FR as [FR1 FR];
         apply (proj1 (rw_cells_app rsegs _ _ [_;_] _)) in FR; destruct FR as [FRA FR2];
         cbn [cells_size csize Nat.add] in FRA, FR2;
         replace (bv_unsigned sp + -544 + Z.of_nat 112)%Z with (bv_unsigned sp + -432)%Z in FRA by lia;
         replace (bv_unsigned sp + -544 + Z.of_nat 112 + Z.of_nat 16)%Z with (bv_unsigned sp + -416)%Z in FR2 by lia;
         name_junk FRA; name_junk FR2.
    lazymatch type of FR1 with rw_cells _ ?mq ?a [?c0; ?c1; ?c2; ?c3; ?c4; C8 sp; ?c6; ?c7; ?c8; ?c9] =>
      assert (FR1' : rw_cells rsegs mq a [c0; c1; c2; c3; c4; C8 (Z_to_bv 64 (bv_unsigned sp + 0)); c6; c7; c8; c9])
        by (rewrite Z.add_0_r, (Z_to_bv_bv_unsigned sp); exact FR1); clear FR1; rename FR1' into FR1 end.
    clear LAS.
    lazymatch type of HF with ro_cells _ ?mq _ _ =>
      assert (FB : bytes_at rsegs mq A (s3_L1 d ++ [Z_to_bv 8 37; Z_to_bv 8 115] ++ s3_L2 d ++ [Z_to_bv 8 0])) by (rewrite <- s3_fmt_bytes; exact (proj2 HF));
      pose proof (bytes_at_prefix rsegs mq A _ _ FB) as SRC1 end.
    destruct d; [ | | | destruct D3]; cbn [s3_fmt s3_L1 s3_L2 s3_la] in *; unfold L1_USAGE, L1_COPEN, L1_RERR, L2_USAGE, L2_NL in *; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in *.
    all: unfold FMT_USAGE, FMT_COPEN, FMT_RERR in HF.
    (* [comment removed for export] *)
    all: zs; zs; zs; sx; br K; clear K.
    all: zs; zs; zs; sx.
    all: zto 0x9ecd0%Z; sub_norm; zs; sx; br K; clear K.
    all: zs; sx; zs; br K; clear K.
    all: zto 0x9e640%Z.
    (* [comment removed for export] *)
    all: try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_FILE); try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_RST); lazymatch type of SRC1 with bytes_at _ _ _ ?L1v =>
           call_icpt (FWX _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ Fa f pend L1v rest A lo) by (fwx_sideS FL5) end.
    all: fwx_post FL5; norm_small; regrab lo VA.
    all: zto 0x9ec60%Z.
    all: hot_qend.
    (* [comment removed for export] *)
    all: hot_qend; apply evt_done.
    all: lazymatch goal with FIq : rw_cells rsegs ?mx Fa _ |- _ =>
      lazymatch type of FIq with context [C8 (Z_to_bv 64 ?wpx) :: C8 (mf_mbz1 f) :: _] =>
        pose proof (file_p5_at mx Fa (mf_set_w f (Z_to_bv 64 wpx) (Z_to_bv 64 (mf_buf f)) (Z_to_bv 64 (mf_buf f + mf_bufsize f))) FL5 FIq) as FAT end end.
    all: hot_eexists_all.
    all: split; [reflexivity|].
    all: split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|].
    all: split; [exact HFP|]; split; [split; assumption|].
    all: split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; [exact FAT|].
    all: split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|].
    all: lazymatch goal with SFq : sfS _ _ _ _ _ _ _ _ _ _ _ |- _ => exact SFq end.
  Qed.

  #[using="PB2 N17 PAD NIN PHI P0 FBV FB3 FB2 FB1 FAR PR ROOM LBR LBF NR BHI B0 FWE FWP FWB FL5 ART ARL VLO GT LO D3 FWXC Clg"] Lemma pcs_head_tail : forall (m : word -> option byte) (ms' : machine_state),
    stk rsegs m lo q -> ro_cells rsegs m A (s3_fmt d) -> ssp_cells m canary ->
    file_at m Fa f -> bytes_at rsegs m B pend -> rw_cells rsegs m wp [CB (length rest) rest] ->
    rw_cells rsegs m q [C8 (Z_to_bv 64 VA)] -> va_area m VA (Z_to_bv 64 P :: vrest) ->
    bytes_at rsegs m P (str ++ Z_to_bv 8 0 :: slack) ->
    mem_inv rsegs m -> SFS m ->
    pcs_cut m ms' ->
    evt rsegs (pcs_mid1 m) ms'.
  Proof.
    intros m ms' ST0 HF0 _ _ BUF0 _ _ _ SB0 _ SF0 CUT.
    pose proof alloc_ceiling_val as CV. unfold pcs_mid1, ARG_RET.
    destruct CUT as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & j40 & ja1 & ja2 & j304 & m1 & -> & MU & WM & MI & ST & HFP
                      & [SSP1 SSP2] & FR1 & FRA & FR2 & FILE & BUF & RST & APC & VAA & SB & SF).
    unfold RA_seql.GOT_SSP, RA_seql.SSP_GUARD, DA_Eg3i.SSP_GUARD, GLOBALS_TOP, RO_TOP, PC2_DEPTH, PRINTF_CORE, IMG_LO, IMG_HI, FILE_LO, FILE_HI, SBUF_LO, SBUF_HI, kHighMemBeg_z, FWX5_RET, INT_MAX in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (ro_cells_bound _ _ _ _ HF0) as AB. rewrite s3_la_size in AB.
    pose proof (bytes_at_bound _ _ _ _ BUF0) as BB.
    pose proof (bytes_at_bound _ _ _ _ SB0) as PB. rewrite length_app in PB. cbn [length] in PB.
    assert (LO0 : (0 <= lo)%Z) by (destruct ST0 as [? _]; assumption).
    assert (Q47 : (bv_unsigned sp + 112 <= 2^47)%Z) by (destruct SF0 as ((_ & _ & _ & _ & _ & (_ & _ & _ & _ & B5 & _) & _) & _); lia).
    clear ST0 HF0 BUF0 SB0 SF0.
    pose proof (s3_la_split d) as LA1.
    (* [comment removed for export] *)
    remember (A + l1)%Z as AP eqn:EAP.
    pose proof FWXC as FWX. unfold fwritex_fit_stmt in FWX. cbv zeta in FWX.
    unfold pc_lits in FR1. unfold pc_saved in FR2. unfold RA_seql.SSP_GUARD in FR1.
    fwx_post FL5; norm_small; regrab lo VA.
    (* [comment removed for export] *)
    hot_qset.
    zs; zs; zs; sx; br K; clear K.
    zs; zs; zs; sx.
    zto 0x9ecd0%Z; sub_norm; zs; sx; br K; clear K.
    zs; sx; zs; br K; clear K.
    zto 0x9e640%Z.
    try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_FILE0); lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
           lazymatch goal with Fq : rw_cells rsegs mx Fa (_ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: C8 (Z_to_bv 64 ?wpx) :: _) |- _ =>
           lazymatch goal with Rq : rw_cells rsegs mx _ [CB _ (skipn ?k rest)] |- _ =>
           lazymatch goal with Bq : bytes_at rsegs mx (mf_buf f) (pend ++ ?x) |- _ =>
             call_icpt (FWX _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ Fa
                          (mf_set_w f (Z_to_bv 64 wpx) (Z_to_bv 64 B) (Z_to_bv 64 (B + N))) (pend ++ x) [] (skipn k rest) _ lo) by (fwx_sideS FL5)
           end end end end.
    fwx_post FL5; norm_small; regrab lo VA.
    (* [comment removed for export] *)
    zto 0x9f078%Z; zs; br K; clear K.
    zto 0x9f9e0%Z.
    lazymatch goal with APq : rw_cells rsegs ?mx (bv_unsigned sp) [C8 (Z_to_bv 64 VA)] |- _ =>
      assert (APC' : rw_cells rsegs mx (bv_unsigned sp) [C8 (Z_to_bv 64 (VA + 8 * 0))]) by (replace (VA + 8 * 0)%Z with VA by lia; exact APq);
      clear APq; rename APC' into APC end.
    try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_APC); try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_FRA); call_lit pop_arg_ptr_spec by
      (first [ reflexivity | symmetry; apply Z_to_bv_bv_unsigned | exact FRA | exact VAA | assumption | lia | exact APC
             | match goal with |- ?G => idtac "POPARG-FAIL:" G; fail end ]).
    try clear FRA; try clear APC; try clear VAA; regrab lo VA; unfold va_area in VAA.
    (* [comment removed for export] *)
    zto 0x9f194%Z; zs; br K; clear K.
    zs; zs; br K; clear K.
    zs; zs; zs.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => lazymatch goal with SBq : bytes_at rsegs mx P _ |- _ => rename SBq into SBc end end.
    call_icpt strnlen_icpt_spec by (idtac;
      lazymatch goal with
      | |- stk _ _ _ _ => rewrite ?unsigned_lit by lia; eassumption
      | |- bytes_at _ _ _ _ => rewrite ?unsigned_lit by lia; exact SBc
      | |- memchr_ok _ _ _ _ => rewrite ?unsigned_lit by lia; apply memchr_ok_cstr; exact NIN || (unfold padP in PAD; exact PAD)
      | |- mem_inv _ _ => assumption
      | |- strnlen_icpt_cells ?mx => lazymatch goal with SFq : sfS _ _ _ _ _ _ _ _ _ _ mx |- _ => exact (proj1 (proj2 SFq)) end
      | |- (_ = 0%Z \/ range_ok ?mx _ _) => rewrite ?unsigned_lit by lia; right; unfold INT_MAX; rewrite memchr_len_cstr by (first [exact NIN| lia]);
            lazymatch goal with SFq : sfS _ _ _ _ _ _ _ _ _ _ mx |- _ => exact (proj2 (proj2 SFq)) end
      | |- (_ \/ _)%type => rewrite ?unsigned_lit by lia; right; lia
      | |- _ => rewrite ?unsigned_lit by lia; unfold STRNLEN_ICPT_STACK, INT_MAX; rewrite ?alloc_ceiling_val; lia
      end || match goal with |- ?G => idtac "SNSIDE-FAIL:" G end).
    try match goal with H : bytes_at _ _ (bv_unsigned _) _ |- _ => rewrite ?unsigned_lit in H by lia end.
    unfold INT_MAX; rewrite (strnlen_res_cstr 0) by exact NIN; rewrite Z.min_l by lia.
    (* [comment removed for export] *)
    zs.
    zs; br K; clear K.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => lazymatch goal with SBq : bytes_at rsegs mx P _ |- _ =>
           pose proof (nul_read _ _ _ _ SBq) as RD end end.
    zs; clear RD.
    zs; br K; clear K.
    zs; zs; zs; zs; zs; zs.
    (* [comment removed for export] *)
    zto 0x9f50c%Z; sub_norm; sx; zs; br K; clear K.
    zs; zs; sx; zs; zs; sx; zs; br K; clear K.
    zs; zs; zs; sx; zs; zs; zs; br K; clear K.
    zs; zs; br K; clear K.
    zto 0x9f558%Z; zs; br K; clear K.
    zto 0x9e640%Z.
    (* [comment removed for export] *)
    try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_FILE); lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
           lazymatch goal with Fq : rw_cells rsegs mx Fa (_ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: C8 (Z_to_bv 64 ?wpx) :: _) |- _ =>
           lazymatch goal with Rq : rw_cells rsegs mx _ [CB _ (skipn ?k rest)] |- _ =>
           lazymatch goal with Bq : bytes_at rsegs mx (mf_buf f) (pend ++ ?x) |- _ =>
             call_icpt (FWX _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ Fa
                          (mf_set_w f (Z_to_bv 64 wpx) (Z_to_bv 64 B) (Z_to_bv 64 (B + N))) (pend ++ x) [] (skipn k rest) 0x10b85%Z lo) by (fwx_sideS FL5)
           end end end end.
    fwx_post FL5; norm_small; regrab lo VA.
    (* [comment removed for export] *)
    zto 0x9f678%Z.
    lazymatch goal with FR1q : rw_cells rsegs ?mx (bv_unsigned sp + -544) _ |- _ =>
      pose proof (rw_cells_read4_C8 rsegs _ _ _ 16 _ (Z_to_bv 64 (bv_unsigned sp + -544 + 16)) FR1q eq_refl ltac:(unfold wa; f_equal; lia)) as RD4 end.
    zs; clear RD4; unfold sx32; zsimp; sx; zs; br K; clear K.
    zto 0x9e640%Z.
    all: hot_qend.
    (* [comment removed for export] *)
    replace (0 + n)%Z with n in * by lia.
    hot_qend; apply evt_done; unfold INT_MAX; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Nat.sub].
    lazymatch goal with FR1q : rw_cells rsegs ?mx (bv_unsigned sp + -544) _ |- _ => apply fr1_recast in FR1q end.
    lazymatch goal with FIq : rw_cells rsegs ?mx Fa _ |- _ =>
      lazymatch type of FIq with context [C8 (Z_to_bv 64 (mf_buf f + Z.of_nat (length pend + ?k)))] =>
        replace (mf_buf f + Z.of_nat (length pend + k))%Z with (mf_buf f + Z.of_nat (length pend) + Z.of_nat k)%Z in * by lia;
        pose proof (file_p5_at mx Fa (mf_set_w f (Z_to_bv 64 (mf_buf f + Z.of_nat (length pend) + Z.of_nat k)) (Z_to_bv 64 (mf_buf f)) (Z_to_bv 64 (mf_buf f + mf_bufsize f))) FL5 FIq) as FAT end end.
    lazymatch goal with APq : rw_cells rsegs ?mx (bv_unsigned sp) [C8 (Z_to_bv 64 (VA + 8 * (0 + 1)))] |- _ =>
      replace (VA + 8 * (0 + 1))%Z with (VA + 8)%Z in APq by lia end.
    hot_eexists_all.
    split; [reflexivity|].
    split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|].
    split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; [exact FAT|].
    split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|].
    split; [split; assumption|].
    lazymatch goal with SFq : sfS _ _ _ _ _ _ _ _ _ _ _ |- _ => exact SFq end.
  Qed.

  #[using="PB2 N17 PAD NIN PHI P0 FBV FB3 FB2 FB1 FAR PR ROOM LBR LBF NR BHI B0 FWE FWP FWB FL5 ART ARL VLO GT LO D3 FWXC Clg"] Lemma pcs_head : forall t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (m : word -> option byte),
    a0 = Z_to_bv 64 Fa -> a1 = Z_to_bv 64 A -> a2 = sp -> a3 = Z_to_bv 64 (q + 96) -> a4 = Z_to_bv 64 (q + 264) ->
    stk rsegs m lo q -> ro_cells rsegs m A (s3_fmt d) -> ssp_cells m canary ->
    file_at m Fa f -> bytes_at rsegs m B pend -> rw_cells rsegs m wp [CB (length rest) rest] ->
    rw_cells rsegs m q [C8 (Z_to_bv 64 VA)] -> va_area m VA (Z_to_bv 64 P :: vrest) ->
    bytes_at rsegs m P (str ++ Z_to_bv 8 0 :: slack) ->
    mem_inv rsegs m -> SFS m ->
    evt rsegs (pcs_mid1 m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PRINTF_CORE) fc None m (seg_rom rsegs)).
  Proof.
    intros until m. intros E0 E1 E2 E3 E4 ST HF SSP FILE BUF RST APC VAA SB MI SF.
    eapply evt_cut.
    - eapply pcs_head_a; eassumption.
    - intros ms' CUT. eapply (pcs_head_tail m ms'); eassumption.
  Qed.

  (* [comment removed for export] *)
  Definition pcs_mid2 (m : word -> option byte) : machine_state -> Prop :=
    fun ms => exists (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
      ms = MS (mkR (Z_to_bv 64 FWX5_RET) (Z_to_bv 64 (q + -544)) gp tp t0 t1 t2 (Z_to_bv 64 37) (Z_to_bv 64 INT_MAX)
                   (Z_to_bv 64 (A + l1 + 2)) (Z_to_bv 64 l2) (Z_to_bv 64 Fa) a3 a4 a5 a6 a7
                   (Z_to_bv 64 (INT_MAX - (n + l1))) (Z_to_bv 64 (n + l1)) (Z_to_bv 64 Fa) (Z_to_bv 64 (A + l1 + 2 + l2)) (Z_to_bv 64 l2)
                   (Z_to_bv 64 (A + l1 + 2)) (Z_to_bv 64 0) (Z_to_bv 64 n) (Z_to_bv 64 l2) (Z_to_bv 64 n) t3 t4 t5 t6)
              F (Z_to_bv 64 FWRITEX_ENTRY) fc None m (seg_rom rsegs).

  Ltac norm_lits A :=
    repeat match goal with |- context [Z.of_nat (S ?k)] => let v := eval vm_compute in (Z.of_nat (S k)) in change (Z.of_nat (S k)) with v in * end;
    repeat match goal with H : context [Z.of_nat (S ?k)] |- _ => let v := eval vm_compute in (Z.of_nat (S k)) in change (Z.of_nat (S k)) with v in * end;
    repeat match goal with |- context [(A + ?a + ?b)%Z] => let v := eval vm_compute in (a + b)%Z in replace (A + a + b)%Z with (A + v)%Z in * by lia end.

  #[using="N17 FAR ROOM ART ARL D3 slack rest pend f Clg"] Lemma pcs_mid : forall t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (m : word -> option byte) (j40 ja2 j304 : list byte) (fx : mfile),
    stk rsegs m lo (q + -544) -> ro_cells rsegs m A (s3_fmt d) -> ssp_cells m canary -> mem_inv rsegs m ->
    FRAME1 m j40 -> rw_cells rsegs m (q + -432) [C8 (Z_to_bv 64 P); CB 8 ja2] -> FRAME2 m j304 ->
    file_at m Fa fx -> mf_flags fx = 5%Z ->
    evt rsegs (pcs_mid2 m)
      (MS (mkR (Z_to_bv 64 ARG_RET) (Z_to_bv 64 (q + -544)) gp tp t0 t1 t2 (Z_to_bv 64 37) (Z_to_bv 64 INT_MAX)
               a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 0) (Z_to_bv 64 l1) (Z_to_bv 64 Fa) (Z_to_bv 64 (A + l1 + 2)) (Z_to_bv 64 0) (Z_to_bv 64 P)
               (Z_to_bv 64 0) (Z_to_bv 64 n) (Z_to_bv 64 n) (Z_to_bv 64 n) t3 t4 t5 t6)
          F (Z_to_bv 64 ARG_RET) fc None m (seg_rom rsegs)).
  Proof.
    intros until fx. intros ST HF [SSP1 SSP2] MI FR1 FRA FR2 FILE FLX.
    pose proof alloc_ceiling_val as CV. unfold pcs_mid2, ARG_RET, FWX5_RET.
    apply (file_at_p5 _ _ _ FLX) in FILE. unfold pfile5, file_cells in FILE. cbn [tl] in FILE.
    unfold RA_seql.GOT_SSP, RA_seql.SSP_GUARD, DA_Eg3i.SSP_GUARD, GLOBALS_TOP, RO_TOP, PC2_DEPTH, INT_MAX, IMG_LO, IMG_HI, FILE_LO, FILE_HI, SBUF_LO, SBUF_HI, kHighMemBeg_z in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (ro_cells_bound _ _ _ _ HF) as AB. rewrite s3_la_size in AB.
    assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl ([] : list ivl) m) as MU. pose proof (wmono_refl rsegs m) as WM.
    unfold pc_lits in FR1. unfold pc_saved in FR2. unfold RA_seql.SSP_GUARD in FR1.
    destruct d; [ | | | destruct D3]; cbn [s3_fmt s3_L1 s3_L2 s3_la] in *; unfold L1_USAGE, L1_COPEN, L1_RERR, L2_USAGE, L2_NL in *; cbn [length] in *.
    all: unfold FMT_USAGE, FMT_COPEN, FMT_RERR in HF.
    all: norm_lits A.
    (* [comment removed for export] *)
    all: hot_qset.
    all: zto 0x9ec60%Z.
    all: zs; zs; zs; sx; br K; clear K.
    all: zs; zs; zs; sx.
    all: zto 0x9ecd0%Z; sub_norm; zs; sx; br K; clear K.
    all: zs; sx; zs; br K; clear K.
    all: zto 0x9e640%Z.
    all: hot_qend.
    all: norm_lits A.
    all: hot_qend; apply evt_done; hot_eexists_all.
    all: match goal with |- ?x = ?y => first [reflexivity | idtac "MIDEQ-FAIL" x y] end.
  Qed.

  (* [comment removed for export] *)
  Definition pcs_ret (m : word -> option byte) : machine_state -> Prop :=
    fun ms => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
      ms = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (l1 + n + l2)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (ret_pc ra) fc None m (seg_rom rsegs)
      /\ stk rsegs m lo q.

  #[using="N17 FAR ROOM ART LO D3 slack rest pend f Clg"] Lemma pcs_tail : forall t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (m : word -> option byte) (j40 ja2 j304 : list byte),
    stk rsegs m lo (q + -544) -> ro_cells rsegs m A (s3_fmt d) -> ssp_cells m canary -> mem_inv rsegs m ->
    FRAME1 m j40 -> rw_cells rsegs m (q + -432) [C8 (Z_to_bv 64 P); CB 8 ja2] -> FRAME2 m j304 ->
    evt rsegs (pcs_ret m)
      (MS (mkR (Z_to_bv 64 FWX5_RET) (Z_to_bv 64 (q + -544)) gp tp t0 t1 t2 (Z_to_bv 64 37) (Z_to_bv 64 INT_MAX)
               a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 (INT_MAX - (n + l1))) (Z_to_bv 64 (n + l1)) (Z_to_bv 64 Fa) (Z_to_bv 64 (A + l1 + 2 + l2)) (Z_to_bv 64 l2)
               (Z_to_bv 64 (A + l1 + 2)) (Z_to_bv 64 0) (Z_to_bv 64 n) (Z_to_bv 64 l2) (Z_to_bv 64 n) t3 t4 t5 t6)
          F (Z_to_bv 64 FWX5_RET) fc None m (seg_rom rsegs)).
  Proof.
    intros until j304. intros ST HF [SSP1 SSP2] MI FR1 FRA FR2.
    pose proof alloc_ceiling_val as CV. unfold pcs_ret.
    unfold RA_seql.GOT_SSP, RA_seql.SSP_GUARD, DA_Eg3i.SSP_GUARD, GLOBALS_TOP, RO_TOP, PC2_DEPTH, FWX5_RET, INT_MAX, IMG_LO, IMG_HI, FILE_LO, FILE_HI, SBUF_LO, SBUF_HI, kHighMemBeg_z in *.
    unfold pc_lits in FR1. unfold pc_saved in FR2. unfold RA_seql.SSP_GUARD in FR1.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (ro_cells_bound _ _ _ _ HF) as AB. rewrite s3_la_size in AB.
    assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl ([] : list ivl) m) as MU. pose proof (wmono_refl rsegs m) as WM.
    destruct d; [ | | | destruct D3]; cbn [s3_fmt s3_L1 s3_L2 s3_la] in *; unfold L1_USAGE, L1_COPEN, L1_RERR, L2_USAGE, L2_NL in *; cbn [length] in *.
    all: unfold FMT_USAGE, FMT_COPEN, FMT_RERR in HF.
    all: norm_lits A.
    all: hot_qset.
    all: zs. (* [comment removed for export] *)
    all: zs; br K; clear K. (* [comment removed for export] *)
    all: zs; zs; zs; sx; br K; clear K.
    all: zs; zs; zs; sx; zs; br K; clear K.
    (* [comment removed for export] *)
    all: zs; br K; clear K.
    all: zto 0x9f998%Z; zs; brf Kc; [ exfalso; apply Kc; reflexivity |]; clear Kc.
    all: lazymatch type of FR1 with rw_cells _ ?mq _ ?cs1 => lazymatch type of FRA with rw_cells _ _ _ ?csa => lazymatch type of FR2 with rw_cells _ _ _ ?cs2 =>
      assert (FR : rw_cells rsegs mq (bv_unsigned sp + -544) (cs1 ++ csa ++ cs2));
      [ apply (proj2 (rw_cells_app rsegs _ _ _ _)); split; [exact FR1|]; cbn [cells_size csize Nat.add];
        apply (proj2 (rw_cells_app rsegs _ _ [_;_] _)); split;
        [ eapply rwc_eq; [exact FRA| lia]
        | cbn [cells_size csize Nat.add]; eapply rwc_eq; [exact FR2| lia] ]
      | clear FR1 FRA FR2; cbn [app] in FR ] end end end.
    all: do 16 zs.
    all: hot_qend.
    all: release_frame FR ST (bv_unsigned sp).
    all: norm_lits A.
    all: try match goal with |- context [Z_to_bv 64 (?a + (n + ?b))%Z] => replace (a + (n + b))%Z with (b + n + a)%Z by lia end.
    all: hot_qend; apply evt_done; hot_eexists_all.
    all: split; [| exact ST].
    all: match goal with |- ?x = ?y => first [reflexivity | idtac "TAILEQ-FAIL" x y] end.
  Qed.
End PC2S.
