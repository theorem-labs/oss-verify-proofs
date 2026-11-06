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
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc.AIcpdmn OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcp2qs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcp0e6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc.AIcpxbj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc.AIcp6d9 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcp7wm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpkua.AIcpilj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpkua OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpya4 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcp3q7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpwpz.AIcpdm8 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpwpz OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpw0i.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import ExN.   (* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
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
Local Ltac icpt_consts_in H ::= unfold MEMSET_ICPT_STACK, FWRITEX_STACK, fwritex_fit_post in H; rewrite ?length_app in H; cbn [length Z.of_nat Nat.sub Nat.add skipn mf_set_w mf_set_write_lbf mf_flags mf_rpos mf_rend mf_close mf_wend mf_wpos mf_mbz1 mf_wbase mf_read mf_write mf_seek mf_buf mf_bufsize mf_prev mf_next mf_fd mf_pipepid mf_lockcount mf_mode mf_lock mf_lbf mf_pad148] in H; rewrite ?Z.add_0_r in H.
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
(* [comment removed for export] *)
From Ltac2 Require Ltac2.
Ltac2 hot_lia_keep_existing names :=
  let hs := Ltac2.List.map (fun h => let (id, _, _) := h in id) (Ltac2.Control.hyps ()) in
  Ltac2.Std.keep (Ltac2.List.filter (fun n => Ltac2.List.exist (fun h => Ltac2.Ident.equal h n) hs) names).
Ltac hot_lia_cut := ltac2:(Ltac2.Control.enter (fun () => hot_lia_keep_existing [@LO; @ROOM; @FAR; @GT; @CV; @LEQ0; @LO0; @Q47; @FB3; @RL; @LEQ; @LEQ1; @LEQ4; @ART; @K; @LEQ2; @LEQ3; @PR; @LBF; @FB2; @ARL; @B0; @BHI; @NR; @LBR; @LEQ5; @VLO; @B5; @SEPq])).
Ltac hot_lia_full := OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Diet8ul.dlia_sec.
Local Ltac lia ::= hot_lia_cut; hot_lia_full.
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
Ltac fwx_range2 :=
  rewrite ?unsigned_lit by lia; rewrite ?length_app; cbn [length Z.of_nat Nat.add];
  lazymatch goal with SFq : sfF _ _ _ _ _ _ _ _ ?mm |- range_ok ?mm ?a ?n =>
    first [ eapply (sfF_buf_range _ _ _ _ _ _ _ _ _ _ _ SFq); lia
          | eapply (sfF_fmt_range _ _ _ _ _ _ _ _ _ _ _ SFq); lia
          | eapply (sfF_stack_range _ _ _ _ _ _ _ _ _ _ _ SFq); lia ] end.
Ltac fwx_side2 FL5 :=
  idtac; cbn [mf_set_w mf_set_write_lbf mf_flags mf_rpos mf_rend mf_close mf_wend mf_wpos mf_mbz1 mf_wbase mf_read mf_write mf_seek mf_buf mf_bufsize mf_prev mf_next mf_fd mf_pipepid mf_lockcount mf_mode mf_lock mf_lbf mf_pad148];
  lazymatch goal with
  | |- file_at ?mx ?fa _ => apply file_p5_at; [exact FL5 | match goal with H : rw_cells rsegs mx fa _ |- _ => exact H end]
  | |- bytes_at _ _ _ [] => apply bytes_at_nil; lia
  | |- bytes_at _ _ _ _ => rewrite ?unsigned_lit by lia; first [eassumption | eapply bytes_at_eqa; [eassumption | rewrite ?length_app; cbn [length]; lia]]
  | |- rw_cells _ _ _ _ => rewrite ?unsigned_lit by lia; first [eassumption | rewrite ?length_app, ?length_skipn; cbn [length Z.of_nat]; eapply rwc_eq; [eassumption | cbn [length]; rewrite ?length_app; cbn [length]; lia]]
  | |- stk _ _ _ _ => rewrite ?unsigned_lit by lia; eassumption
  | |- mem_inv _ _ => eassumption
  | |- memcpy_icpt_cells _ => lazymatch goal with SFq : sfF _ _ _ _ _ _ _ _ _ |- _ => exact (proj1 SFq) end
  | |- @eq _ _ _ => rewrite ?unsigned_lit by lia; first [reflexivity | assumption | cbn; f_equal; lia | cbn; rewrite ?length_app, ?length_skipn; cbn; first [f_equal; lia | lia]]
  | |- (_ \/ ~ In _ _)%type => left; cbn; lia
  | |- (_ = 0%Z \/ _)%type => first [left; reflexivity | left; cbn; lia | right; split; fwx_range2]
  | |- _ \/ _ => rewrite ?unsigned_lit by lia; rewrite ?Z.add_0_r, ?length_app; cbn [length Z.of_nat Nat.add]; lia
  | |- _ => rewrite ?unsigned_lit by lia; unfold FWRITEX_STACK; rewrite ?length_app, ?length_skipn; cbn [length Z.of_nat Nat.add]; lia
  end || match goal with |- ?G => idtac "FWXSIDE-FAIL:" G end.

(* [comment removed for export] *)
Ltac drop_stale_bufs :=
  repeat match goal with H1 : bytes_at rsegs ?m ?b ?l1, H2 : bytes_at rsegs ?m' ?b' (?l1' ++ _) |- _ =>
    constr_eq m m'; constr_eq b b'; constr_eq l1 l1'; clear H1 end.

Definition T_UINT : Z := 11.

(* [comment removed for export] *)
Lemma pop_arg_uint_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (ARG AP VA : Z) (slots : list word) (i : Z) (v : word) (old1 old2 : list byte),
  a0 = Z_to_bv 64 ARG -> a1 = Z_to_bv 64 T_UINT -> a2 = Z_to_bv 64 AP ->
  rw_cells rsegs m ARG [CB 8 old1; CB 8 old2] -> rw_cells rsegs m AP [C8 (Z_to_bv 64 (VA + 8 * i))] -> va_area m VA slots ->
  nth_error slots (Z.to_nat i) = Some v -> (0 <= i)%Z ->
  (ARG + 16 <= AP \/ AP + 8 <= ARG)%Z -> (AP + 8 <= VA)%Z -> (ARG + 16 <= VA)%Z ->
  mem_inv rsegs m ->
  evt rsegs (pop_arg_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ARG AP VA slots i (zx32 v) old2 m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x9f9e0) fc None m (seg_rom rsegs)).
Proof.
  intros until old2. intros -> -> -> HA HP HV Hn Hi SEP1 SEP2 SEP3 MI. unfold T_UINT. unfold va_area in HV.
  pose proof (munch_refl [(ARG, ARG + 16); (AP, AP + 8)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
  pose proof (rw_cells_bound _ _ _ _ HA) as B1. pose proof (rw_cells_bound _ _ _ _ HP) as B2. pose proof (bytes_at_bound _ _ _ _ HV) as B3.
  cbn [cells_size csize Nat.add] in B1, B2. rewrite u64s_length in B3. pose proof (nth_error_lt _ _ _ Hn) as IL.
  do 3 zs. if_lit. do 7 zs.
  zs. zs. zs.
  pose proof (va_read4 _ VA slots i v (Z_to_bv 64 (VA + 8 * i)) HV Hn Hi eq_refl) as RD.
  zs. zs. zs.
  replace (VA + 8 * i + 8)%Z with (VA + 8 * (i + 1))%Z in * by lia.
  finish. all: unfold va_area; assumption.
Qed.

Local Ltac fok_lemma P ::= lazymatch P with
  | sfF ?A ?la ?B ?N ?SB ?K ?zlo ?zhi => constr:(fok_sfF A la B N SB K zlo zhi ltac:(lia) ltac:(lia))
  | _ => fok_lemma_base P end.
Local Ltac solve_wfok ::= cbn [wfok]; rewrite ?length_app, ?length_skipn;
  cbn [length Z.of_nat mf_set_w mf_buf mf_bufsize]; unfold kHighMemBeg_z, FILE_LO, FILE_HI, SBUF_LO, SBUF_HI in *; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try exact I; lia.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= refok_store_hook m a bs n Hn Ha Hl.
Local Ltac transport_call_extra segs W m m' MU WM ::= refok_all W m m' MU.
Local Ltac icpt_relow W m m' MU ::= refok_all W m m' MU.

Definition zb8 (l : list Z) : list byte := map (fun z => Z_to_bv 8 z) l.
Definition U_L1 : list byte := Eval cbv [zb8 map] in zb8 [99; 108; 105; 58; 32; 105; 110; 112; 117; 116; 32; 62; 61; 32]%Z.            (* [comment removed for export] *)
Definition U_DIG : list byte := Eval cbv [zb8 map] in zb8 [54; 55; 49; 48; 56; 56; 54; 52]%Z.                                  (* [comment removed for export] *)
Definition U_L2 : list byte := Eval cbv [zb8 map] in zb8 [32; 98; 121; 116; 101; 115; 44; 32; 114; 101; 102; 117; 115; 101; 100; 10]%Z.  (* [comment removed for export] *)
Definition U_MSG : list byte := Eval cbv [U_L1 U_DIG U_L2 app] in (U_L1 ++ U_DIG ++ U_L2).
Lemma U_fmt_bytes : cells_bytes FMT_REFUSED = U_L1 ++ [Z_to_bv 8 37; Z_to_bv 8 117] ++ U_L2 ++ [Z_to_bv 8 0].
Proof. reflexivity. Qed.
(* [comment removed for export] *)

Ltac norm_lits A :=
  repeat match goal with |- context [Z.of_nat (S ?k)] => let v := eval vm_compute in (Z.of_nat (S k)) in change (Z.of_nat (S k)) with v in * end;
  repeat match goal with H : context [Z.of_nat (S ?k)] |- _ => let v := eval vm_compute in (Z.of_nat (S k)) in change (Z.of_nat (S k)) with v in * end;
  repeat match goal with |- context [(A + ?a + ?b)%Z] => let v := eval vm_compute in (a + b)%Z in replace (A + a + b)%Z with (A + v)%Z in * by lia end.

Section PC2U.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (lo A Fa VA : Z) (canary : word) (f : mfile) (pend rest : list byte) (vrest : list word) (ZSB : Z) (ZK : nat).
  Hypothesis FWXC : fwritex_fit_stmt.
  #[local] Notation q := (bv_unsigned sp).
  #[local] Notation B := (mf_buf f).
  #[local] Notation N := (mf_bufsize f).
  #[local] Notation wp := (mf_buf f + Z.of_nat (length pend))%Z.
  Hypothesis LO : (lo <= q - PC2_DEPTH)%Z.
  Hypothesis GT : (alloc_ceiling <= lo)%Z.   (* [comment removed for export] *)
  Hypothesis VLO : (q + 368 <= VA)%Z.
  Hypothesis VHI : (VA + 48 <= 2^63)%Z.
  Hypothesis ARL : (IMG_LO <= A)%Z.
  Hypothesis ART : (A + 33 <= RO_TOP)%Z.
  Hypothesis FL5 : mf_flags f = 5%Z.
  Hypothesis FWB : mf_wbase f = Z_to_bv 64 B.
  Hypothesis FWP : mf_wpos f = Z_to_bv 64 wp.
  Hypothesis FWE : mf_wend f = Z_to_bv 64 (B + N).
  Hypothesis B0 : (0 < B)%Z.
  Hypothesis BHI : (B + N < 2^47)%Z.
  Hypothesis NR : (0 <= N < 2^31)%Z.
  Hypothesis LBF : (mf_lbf f < 0)%Z.
  Hypothesis LBR : (-2^31 <= mf_lbf f)%Z.
  Hypothesis ROOM : (Z.of_nat (length pend) + 38 <= N)%Z.
  Hypothesis PR : (Z.of_nat (length pend) + Z.of_nat (length rest) = N)%Z.
  Hypothesis FAR : (FILE_LO <= Fa /\ Fa + 152 <= FILE_HI)%Z.
  Hypothesis FB1 : (Fa + 152 <= B \/ B + N <= Fa)%Z.
  Hypothesis FB2 : (B + N <= lo \/ q + 16 <= B)%Z.
  Hypothesis FB3 : ((SBUF_LO <= B /\ B + N <= SBUF_HI) \/ kHighMemBeg_z <= B)%Z.
  Hypothesis FBV : (B + N <= VA)%Z.
  Notation SFF m1 := (sfF A 33 B N ZSB ZK (q - PC2_DEPTH) (q + 96) m1).

  Definition pcu_ret (m : word -> option byte) : machine_state -> Prop :=
    fun ms => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : word -> option byte),
      ms = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 38) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (ret_pc ra) fc None m' (seg_rom rsegs)
      /\ munch [(q - PC2_DEPTH, q + 8); (Fa, Fa + 152); (wp, wp + 38)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
      /\ stk rsegs m' lo q
      /\ file_at m' Fa (mf_set_w f (Z_to_bv 64 (wp + 38)) (Z_to_bv 64 B) (Z_to_bv 64 (B + N)))
      /\ bytes_at rsegs m' B (pend ++ U_MSG)
      /\ rw_cells rsegs m' (wp + 38) [CB (length rest - 38)%nat (skipn 38 rest)]
      /\ rw_cells rsegs m' q [C8 (Z_to_bv 64 (VA + 8))]
      /\ ssp_cells m' canary /\ SFF m'.

  #[using="FBV FB3 FB2 FB1 FAR PR ROOM LBR LBF NR BHI B0 FWE FWP FWB FL5 ART ARL VLO GT LO FWXC Clg"] Lemma pcu_all : forall t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (m : word -> option byte),
    a0 = Z_to_bv 64 Fa -> a1 = Z_to_bv 64 A -> a2 = sp -> a3 = Z_to_bv 64 (q + 96) -> a4 = Z_to_bv 64 (q + 264) ->
    stk rsegs m lo q -> ro_cells rsegs m A FMT_REFUSED -> ssp_cells m canary ->
    file_at m Fa f -> bytes_at rsegs m B pend -> rw_cells rsegs m wp [CB (length rest) rest] ->
    rw_cells rsegs m q [C8 (Z_to_bv 64 VA)] -> va_area m VA (Z_to_bv 64 67108864 :: vrest) ->
    mem_inv rsegs m -> SFF m ->
    evt rsegs (pcu_ret m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PRINTF_CORE) fc None m (seg_rom rsegs)).
  Proof.
    intros until m. intros -> -> -> -> -> ST HF [SSP1 SSP2] FILE BUF RST APC VAA MI SF.
    pose proof alloc_ceiling_val as CV. (* [comment removed for export] *)
    unfold RA_seql.GOT_SSP, RA_seql.SSP_GUARD, DA_Eg3i.SSP_GUARD, GLOBALS_TOP, RO_TOP, PC2_DEPTH, PRINTF_CORE, IMG_LO, IMG_HI, FILE_LO, FILE_HI, SBUF_LO, SBUF_HI, kHighMemBeg_z in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (ro_cells_bound _ _ _ _ HF) as AB. cbn [cells_size csize Nat.add FMT_REFUSED length] in AB.
    pose proof (bytes_at_bound _ _ _ _ BUF) as BB. pose proof (rw_CB_length _ _ _ _ _ RST) as RL.
    assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(bv_unsigned sp - 4928, bv_unsigned sp + 8); (Fa, Fa + 152); (mf_buf f + Z.of_nat (length pend), mf_buf f + Z.of_nat (length pend) + 38)]%Z m) as MU.
    pose proof (wmono_refl rsegs m) as WM.
    unfold va_area in VAA.
    apply (file_at_p5 _ _ _ FL5) in FILE. unfold pfile5, file_cells in FILE. cbn [tl] in FILE.
    pose proof FWXC as FWX. unfold fwritex_fit_stmt in FWX. cbv zeta in FWX.
    assert (Q47 : (bv_unsigned sp + 112 <= 2^47)%Z) by (destruct SF as (_ & _ & _ & _ & _ & (_ & _ & _ & _ & B5 & _) & _); lia).
    assert (FB : bytes_at rsegs m A (U_L1 ++ [Z_to_bv 8 37; Z_to_bv 8 117] ++ U_L2 ++ [Z_to_bv 8 0])) by (rewrite <- U_fmt_bytes; exact (proj2 HF)).
    pose proof (bytes_at_prefix rsegs m A _ _ FB) as SRC1.
    pose proof (bytes_at_app_r m _ _ _ (bytes_at_app_r m A _ _ FB)) as FMB. pose proof (bytes_at_prefix rsegs m _ _ _ FMB) as SRC5. clear FMB.
    unfold U_L1, U_L2 in *. cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in *. norm_lits A.
    unfold FMT_REFUSED in HF.
    rewrite <- (Z_to_bv_bv_unsigned sp) at 1.
    fwx_leqs.
    carve_frame 544%nat ST.
    do 43 zs. name_junk FR.
    apply (rw_cells_split_CB rsegs _ _ [_;_;_;_;_;_;_;_;_;_] 320 _ _ [8; 8; 304]%nat) in FR; [|reflexivity].
    cbn [mk_CB_cells app] in FR.
    apply (proj1 (rw_cells_app rsegs _ _ [_;_;_;_;_;_;_;_;_;_] _)) in FR. destruct FR as [FR1 FR].
    apply (proj1 (rw_cells_app rsegs _ _ [_;_] _)) in FR. destruct FR as [FRA FR2].
    cbn [cells_size csize Nat.add] in FRA, FR2.
    replace (bv_unsigned sp + -544 + Z.of_nat 112)%Z with (bv_unsigned sp + -432)%Z in FRA by lia.
    replace (bv_unsigned sp + -544 + Z.of_nat 112 + Z.of_nat 16)%Z with (bv_unsigned sp + -416)%Z in FR2 by lia.
    name_junk FRA. name_junk FR2.
    lazymatch type of FR1 with rw_cells _ ?mq ?a [?c0; ?c1; ?c2; ?c3; ?c4; C8 sp; ?c6; ?c7; ?c8; ?c9] =>
      assert (FR1' : rw_cells rsegs mq a [c0; c1; c2; c3; c4; C8 (Z_to_bv 64 (bv_unsigned sp + 0)); c6; c7; c8; c9])
        by (rewrite Z.add_0_r, (Z_to_bv_bv_unsigned sp); exact FR1); clear FR1; rename FR1' into FR1 end.
    (* [comment removed for export] *)
    zs. zs. zs. sx. br K. clear K.
    zs. zs. zs. sx.
    zto 0x9ecd0%Z. sub_norm. zs. sx. br K. clear K.
    zs. sx. zs. br K. clear K.
    zto 0x9e640%Z.
    try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_FILE); try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_RST); lazymatch type of SRC1 with bytes_at _ _ _ ?L1v =>
      call_icpt (FWX _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ Fa f pend L1v rest A lo) by (fwx_side2 FL5) end.
    fwx_post FL5. norm_small. drop_stale_bufs. regrab lo VA.
    zto 0x9ec60%Z.
    (* [comment removed for export] *)
    zs. zs. zs. sx. br K. clear K.
    zs. zs. zs. sx.
    zto 0x9ecd0%Z. sub_norm. zs. sx. br K. clear K.
    zs. sx. zs. br K. clear K.
    zto 0x9e640%Z.
    try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_FILE); lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      lazymatch goal with Fq : rw_cells rsegs mx Fa (_ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: C8 (Z_to_bv 64 ?wpx) :: _) |- _ =>
      lazymatch goal with Bq : bytes_at rsegs mx (mf_buf f) ?pdx |- _ =>
        call_icpt (FWX _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ Fa
                     (mf_set_w f (Z_to_bv 64 wpx) (Z_to_bv 64 B) (Z_to_bv 64 (B + N))) pdx [] (skipn 14 rest) _ lo) by (fwx_side2 FL5)
      end end end.
    fwx_post FL5. norm_small. drop_stale_bufs. regrab lo VA.
    (* [comment removed for export] *)
    zto 0x9f078%Z. zs. br K. clear K.
    zto 0x9f9e0%Z.
    lazymatch goal with APq : rw_cells rsegs ?mx (bv_unsigned sp) [C8 (Z_to_bv 64 VA)] |- _ =>
      assert (APC' : rw_cells rsegs mx (bv_unsigned sp) [C8 (Z_to_bv 64 (VA + 8 * 0))]) by (replace (VA + 8 * 0)%Z with VA by lia; exact APq);
      clear APq; rename APC' into APC end.
    try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_APC); try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_FRA); call_lit pop_arg_uint_spec by
      (first [ reflexivity | symmetry; apply Z_to_bv_bv_unsigned | exact FRA | exact VAA | assumption | lia | exact APC
             | match goal with |- ?G => idtac "POPARG-FAIL:" G; fail end ]).
    try clear FRA; try clear APC; try clear VAA. regrab lo VA. unfold va_area in VAA.
    change (zx32 (Z_to_bv 64 67108864)) with (Z_to_bv 64 67108864) in *.
    (* [comment removed for export] *)
    zto 0x9e640%Z.
    try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_FILE); lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      lazymatch goal with Fq : rw_cells rsegs mx Fa (_ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: C8 (Z_to_bv 64 ?wpx) :: _) |- _ =>
      lazymatch goal with Rq : rw_cells rsegs mx _ [CB _ (skipn ?k rest)] |- _ =>
      lazymatch goal with Bq : bytes_at rsegs mx (mf_buf f) ?pdx |- _ =>
        call_icpt (FWX _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ Fa
                     (mf_set_w f (Z_to_bv 64 wpx) (Z_to_bv 64 B) (Z_to_bv 64 (B + N))) pdx [] (skipn k rest) 0x10b85%Z lo) by (fwx_side2 FL5)
      end end end end.
    fwx_post FL5. norm_small. drop_stale_bufs. regrab lo VA.
    (* [comment removed for export] *)
    zto 0x9f678%Z.
    lazymatch goal with FR1q : rw_cells rsegs ?mx (bv_unsigned sp + -544) _ |- _ =>
      pose proof (rw_cells_read4_C8 rsegs _ _ _ 16 _ (Z_to_bv 64 (bv_unsigned sp + -544 + 16)) FR1q eq_refl ltac:(unfold wa; f_equal; lia)) as RD4 end.
    zs. clear RD4. unfold sx32. zsimp. sx. zs. br K. clear K.
    zto 0x9e640%Z.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      lazymatch goal with FR2q : rw_cells rsegs mx (bv_unsigned sp + -416) (CB 40 ?ja :: ?restc) |- _ =>
        pose proof (proj2 (proj1 (proj2 (proj1 (rw_cells_app rsegs _ _ [CB 40 ja] restc) FR2q)))) as SRC4;
        cbn [cells_size csize Nat.add cells_bytes cbytes app] in SRC4;
        apply (bytes_at_prefix rsegs mx _ [_;_;_;_;_;_;_;_]) in SRC4;
        match type of SRC4 with bytes_at _ _ ?ax _ => replace ax with (bv_unsigned sp + -376)%Z in SRC4 by (cbn; lia) end
      end end.
    try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_FILE); try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_RST); lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      lazymatch goal with Fq : rw_cells rsegs mx Fa (_ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: C8 (Z_to_bv 64 ?wpx) :: _) |- _ =>
      lazymatch goal with Rq : rw_cells rsegs mx _ [CB _ (skipn ?k rest)] |- _ =>
      lazymatch goal with Bq : bytes_at rsegs mx (mf_buf f) ?pdx |- _ =>
      lazymatch type of SRC4 with bytes_at _ _ _ ?dg =>
        call_icpt (FWX _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ Fa
                     (mf_set_w f (Z_to_bv 64 wpx) (Z_to_bv 64 B) (Z_to_bv 64 (B + N))) pdx dg (skipn k rest) (bv_unsigned sp + -376)%Z lo) by (fwx_side2 FL5)
      end end end end end.
    fwx_post FL5. norm_small. drop_stale_bufs. regrab lo VA. clear SRC4.
    repeat match goal with H : context [skipn ?a (skipn ?b ?r)] |- _ => rewrite skipn_skipn in H; cbn [Nat.add] in H end.
    repeat match goal with H : rw_cells rsegs _ _ [CB (length (skipn ?a ?r) - _)%nat _] |- _ => rewrite length_skipn in H end.
    repeat match goal with H : rw_cells rsegs _ _ [CB (?a - ?b - ?c)%nat _] |- _ =>
      let v := eval vm_compute in (b + c)%nat in replace (a - b - c)%nat with (a - v)%nat in H by lia end.
    (* [comment removed for export] *)
    zto 0x9ec60%Z.
    zs. zs. zs. sx. br K. clear K.
    zs. zs. zs. sx.
    zto 0x9ecd0%Z. sub_norm. zs. sx. br K. clear K.
    zs. sx. zs. br K. clear K.
    zto 0x9e640%Z.
    try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_FILE); try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_RST); lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      lazymatch goal with Fq : rw_cells rsegs mx Fa (_ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: C8 (Z_to_bv 64 ?wpx) :: _) |- _ =>
      lazymatch goal with Rq : rw_cells rsegs mx _ [CB _ (skipn ?k rest)] |- _ =>
      lazymatch goal with Bq : bytes_at rsegs mx (mf_buf f) ?pdx |- _ =>
      lazymatch type of SRC5 with bytes_at _ _ ?a5 ?l5 =>
        call_icpt (FWX _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ Fa
                     (mf_set_w f (Z_to_bv 64 wpx) (Z_to_bv 64 B) (Z_to_bv 64 (B + N))) pdx l5 (skipn k rest) a5 lo) by (fwx_side2 FL5)
      end end end end end.
    fwx_post FL5. norm_small. drop_stale_bufs. regrab lo VA.
    (* [comment removed for export] *)
    zs. zs. br K. clear K.
    zs. zs. zs. sx. br K. clear K.
    zs. zs. zs. sx. zs. br K. clear K.
    zs. br K. clear K.
    zto 0x9f998%Z. zs. brf Kc. { exfalso. apply Kc. reflexivity. } clear Kc.
    lazymatch goal with FR1 : rw_cells rsegs ?mq (bv_unsigned sp + -544) ?cs1 |- _ =>
      lazymatch goal with FRA : rw_cells rsegs mq (bv_unsigned sp + -432) ?csa |- _ =>
      lazymatch goal with FR2 : rw_cells rsegs mq (bv_unsigned sp + -416) ?cs2 |- _ =>
      assert (FR : rw_cells rsegs mq (bv_unsigned sp + -544) (cs1 ++ csa ++ cs2));
      [ apply (proj2 (rw_cells_app rsegs _ _ _ _)); split; [exact FR1|]; cbn [cells_size csize Nat.add];
        apply (proj2 (rw_cells_app rsegs _ _ [_;_] _)); split;
        [ eapply rwc_eq; [exact FRA| lia]
        | cbn [cells_size csize Nat.add]; eapply rwc_eq; [exact FR2| cbn; lia] ]
      | clear FR1 FRA FR2; cbn [app] in FR ] end end end.
    do 16 zs.
    lazymatch goal with STq : stk rsegs _ lo _ |- _ => release_frame FR STq (bv_unsigned sp); rename STq into STf end.
    (* [comment removed for export] *)
    repeat match goal with H : context [skipn ?a (skipn ?b ?r)] |- _ => rewrite skipn_skipn in H; cbn [Nat.add] in H end.
    repeat match goal with H : rw_cells rsegs _ _ [CB (length (skipn ?a ?r) - _)%nat _] |- _ => rewrite length_skipn in H end.
    repeat match goal with H : rw_cells rsegs _ _ [CB (?a - ?b - ?c)%nat _] |- _ =>
      let v := eval vm_compute in (b + c)%nat in replace (a - b - c)%nat with (a - v)%nat in H by lia end.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      lazymatch goal with Rq : rw_cells rsegs mx ?ar [CB _ (skipn 38 rest)] |- _ =>
        replace ar with (mf_buf f + Z.of_nat (length pend) + 38)%Z in Rq by (rewrite ?length_app; cbn [length]; lia) end;
      lazymatch goal with FIq : rw_cells rsegs mx Fa (_ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: C8 (Z_to_bv 64 ?wpx) :: _) |- _ =>
        replace wpx with (mf_buf f + Z.of_nat (length pend) + 38)%Z in FIq by (rewrite ?length_app; cbn [length]; lia);
        pose proof (file_p5_at mx Fa (mf_set_w f (Z_to_bv 64 (mf_buf f + Z.of_nat (length pend) + 38)) (Z_to_bv 64 (mf_buf f)) (Z_to_bv 64 (mf_buf f + mf_bufsize f))) FL5 FIq) as FAT end;
      lazymatch goal with APq : rw_cells rsegs mx (bv_unsigned sp) [C8 (Z_to_bv 64 (VA + 8 * (0 + 1)))] |- _ =>
        replace (VA + 8 * (0 + 1))%Z with (VA + 8)%Z in APq by lia end;
      lazymatch goal with Bq : bytes_at rsegs mx (mf_buf f) _ |- _ =>
        rewrite <- !app_assoc in Bq; cbn [app] in Bq; change U_L1 with U_L1 in Bq || idtac end
    end.
    apply evt_done. unfold pcu_ret. unfold RA_seql.GOT_SSP, RA_seql.SSP_GUARD, DA_Eg3i.SSP_GUARD, GLOBALS_TOP, RO_TOP, PC2_DEPTH, PRINTF_CORE, IMG_LO, IMG_HI, FILE_LO, FILE_HI, SBUF_LO, SBUF_HI, kHighMemBeg_z. fold U_MSG.
    hot_eexists_all.
    split; [reflexivity|].
    split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [exact STf|].
    split; [exact FAT|].
    split. { lazymatch goal with Bq : bytes_at rsegs _ (mf_buf f) (pend ++ ?l) |- _ => unfold U_MSG; exact Bq end. }
    split; [eassumption|]. split; [eassumption|].
    split; [split; assumption|].
    lazymatch goal with SFq : sfF _ _ _ _ _ _ _ _ _ |- _ => exact SFq end.
  Qed.
End PC2U.
