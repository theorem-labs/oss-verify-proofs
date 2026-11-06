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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import PF_file.
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
Local Ltac icpt_consts_in H ::= unfold MEMSET_ICPT_STACK, FWRITEX_STACK, fwritex_fit_post in H; cbn [length Z.of_nat Nat.sub skipn mf_set_w mf_set_write_lbf mf_flags mf_rpos mf_rend mf_close mf_wend mf_wpos mf_mbz1 mf_wbase mf_read mf_write mf_seek mf_buf mf_bufsize mf_prev mf_next mf_fd mf_pipepid mf_lockcount mf_mode mf_lock mf_lbf mf_pad148] in H; rewrite ?Z.add_0_r in H.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require MliaFast.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MliaFast.mlia_fast | lia | Z.div_mod_to_equations; lia | Z.div_mod_to_equations; nia ].
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
Ltac hot_lia_cut := ltac2:(Ltac2.Control.enter (fun () => hot_lia_keep_existing [@LO; @FAR; @GT; @ROOM; @CV; @LO0; @Q47; @FB3; @RL; @LEQ; @LEQ0; @FB2; @K; @ART; @PR; @ARL; @LEQ1; @B0; @BHI; @NR; @LBF; @H1; @H2; @H3; @VLO; @AB; @SBL; @B3; @W; @B5; @SEPq; @LEQ2])).
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
Definition sfF (A la B N : Z) (SB : Z) (K : nat) (zlo zhi : Z) (m : word -> option byte) : Prop :=
  asan_memcpy_cells m /\ asan_memset_cells m /\ range_ok m A la /\ range_ok m B N /\ bytes_at rsegs m SB (zeros K) /\ zsh_bounds SB K zlo zhi /\ (2147446784 <= SB)%Z.   (* [comment removed for export] *)
Lemma fok_sfF : forall A la B N SB K zlo zhi, (0 <= la)%Z -> (0 <= N)%Z -> fokP (sfF A la B N SB K zlo zhi).
Proof.
  intros A la B N SB K zlo zhi Hla HN W m m' MU HW (C1 & C2 & R1 & R2 & ZS & ZB & SBL). pose proof ZB as (B1 & B2 & B3 & B4 & B5 & B6).
  split; [exact (fok_asan_memcpy_cells W m m' MU HW C1)|]. split; [exact (fok_asan_memset_cells W m m' MU HW C2)|].
  split; [exact (fok_range_ok A la Hla W m m' MU HW R1)|]. split; [exact (fok_range_ok B N HN W m m' MU HW R2)|].
  split; [|exact (conj ZB SBL)]. eapply bytes_at_transport; [exact ZS| exact MU| apply wfok_disjoint; [exact HW| | lia]].
  unfold far, SBUF_HI, kHighShadowEnd_z, kHighMemBeg_z, sha, shadow_off in *. right; right. rewrite zeros_length. lia.
Qed.
Lemma sfF_buf_range : forall A la B N SB K zlo zhi m a n,
  sfF A la B N SB K zlo zhi m -> (B <= a)%Z -> (a + n <= B + N)%Z -> (1 <= n)%Z -> range_ok m a n.
Proof. intros until n. intros (_ & _ & _ & R & _) H1 H2 H3. eapply range_ok_sub; [exact R| lia| lia| lia]. Qed.
Lemma sfF_fmt_range : forall A la B N SB K zlo zhi m a n,
  sfF A la B N SB K zlo zhi m -> (A <= a)%Z -> (a + n <= A + la)%Z -> (1 <= n)%Z -> range_ok m a n.
Proof. intros until n. intros (_ & _ & R & _) H1 H2 H3. eapply range_ok_sub; [exact R| lia| lia| lia]. Qed.
Lemma sfF_stack_range : forall A la B N SB K zlo zhi m a n,
  sfF A la B N SB K zlo zhi m -> (zlo <= a)%Z -> (a + n <= zhi)%Z -> (1 <= n)%Z -> range_ok m a n.
Proof. intros until n. intros (_ & _ & _ & _ & ZS & ZB & _) H1 H2 H3. eapply range_ok_of_zeros; [exact ZS| exact ZB| lia| lia| lia]. Qed.

Local Ltac fok_lemma P ::= lazymatch P with
  | sfF ?A ?la ?B ?N ?SB ?K ?zlo ?zhi => constr:(fok_sfF A la B N SB K zlo zhi ltac:(lia) ltac:(lia))
  | _ => fok_lemma_base P end.
Local Ltac solve_wfok ::= try (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); cbn [wfok]; rewrite ?length_app, ?length_skipn;
  cbn [length Z.of_nat mf_set_w mf_buf mf_bufsize]; unfold kHighMemBeg_z, FILE_LO, FILE_HI, SBUF_LO, SBUF_HI in *; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try exact I; lia.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= refok_store_hook m a bs n Hn Ha Hl.
Local Ltac transport_call_extra segs W m m' MU WM ::= refok_all W m m' MU.
Local Ltac icpt_relow W m m' MU ::= refok_all W m m' MU.

Definition FWX5_RET : Z := 0x9ecf8.

Lemma cb3_recast : forall segs m a n1 n2 n3 (l1 l2 l3 : list byte) rest,
  rw_cells segs m a (CB n1 l1 :: CB n2 l2 :: CB n3 l3 :: rest) ->
  rw_cells segs m a (CB (n1 + n2 + n3) (l1 ++ l2 ++ l3) :: rest).
Proof.
  intros. eapply rw_cells_recast; [exact H| |].
  - destruct H as [[W _] _]. cbn [cells_wf cell_wf] in W |- *. split; [rewrite !length_app; lia|tauto].
  - cbn [cells_bytes cbytes]. rewrite <- !app_assoc. reflexivity.
Qed.

Lemma bytes_at_eqa : forall m a a' (bs : list byte), bytes_at rsegs m a bs -> a = a' -> bytes_at rsegs m a' bs.
Proof. intros m a a' bs H <-. exact H. Qed.

Ltac norm_small := cbn [length app] in *; try change (Z.of_nat 1) with 1%Z in *; try change (Z.of_nat 0) with 0%Z in *;
  repeat match goal with H : context [(?x + 0)%Z] |- _ => lazymatch x with bv_unsigned _ => fail | _ => rewrite (Z.add_0_r x) in H end end.

(* [comment removed for export] *)
Ltac regrab lo VA :=
  try match goal with H : stk rsegs _ lo _ |- _ => let n := fresh "ST" in rename H into n end;
  try match goal with H : rw_cells rsegs _ (bv_unsigned ?spx + -432) _ |- _ => let n := fresh "FRA" in rename H into n end;
  try match goal with H : rw_cells rsegs _ (bv_unsigned ?spx) [C8 _] |- _ => let n := fresh "APC" in rename H into n end;
  try match goal with H : va_area _ VA _ |- _ => unfold va_area in H end;
  try match goal with H : bytes_at rsegs _ VA _ |- _ => let n := fresh "VAA" in rename H into n end;
  try match goal with H : mem_inv rsegs _ |- _ => let n := fresh "MI" in rename H into n end.

(* [comment removed for export] *)
Ltac leq_nat_num N := lazymatch N with O => idtac | S ?k => leq_nat_num k end.
Ltac leq_zof N :=
  lazymatch N with
  | (?a + ?b)%nat => let x := leq_zof a in let y := leq_zof b in constr:((x + y)%Z)
  | (?a - ?b)%nat => let x := leq_zof a in let y := leq_zof b in constr:((x - y)%Z)
  | O => constr:(0%Z)
  | S ?a => constr:(ltac:(first [ leq_nat_num N; let v := eval cbv in (Z.of_nat N) in exact v
                               | let x := leq_zof a in exact (x + 1)%Z ]) : Z)
  | _ => constr:(Z.of_nat N)
  end.
Ltac leq_pose T :=
  lazymatch T with
  | Z.of_nat (length _) => idtac
  | Z.of_nat ?N =>
      let rhs := leq_zof N in
      lazymatch goal with
      | _ : T = rhs |- _ => idtac
      | _ => let E := fresh "LEQ" in assert (E : T = rhs) by (first [ exact (Nat2Z.inj_add _ _) | lia ])
      end
  | _ => idtac
  end.
Ltac leq_nat_size bs :=
  lazymatch bs with
  | (?a ++ ?b)%list => let x := leq_nat_size a in let y := leq_nat_size b in constr:((x + y)%nat)
  | _ => constr:(length bs)
  end.
Ltac leq_norm T := eval cbn [cells_size csize length cbytes Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in T.
(* [comment removed for export] *)
Definition dl_sep (P : Prop) : Prop := P.
Ltac leq_dedupe :=
  repeat match goal with
  | H1 : rw_cells rsegs ?m _ [CB ?k ?bs], H2 : rw_cells rsegs ?m (mf_buf _ + Z.of_nat (length _ + _))%Z [CB ?k ?bs] |- _ => clear H2
  | H1 : bytes_at rsegs ?m (mf_buf ?f) ?l, H2 : bytes_at rsegs ?m (mf_buf ?f) ?l |- _ => clear H2
  end.
Ltac leq_sep a T :=
  try match goal with
  | FBq : (mf_buf ?f + mf_bufsize ?f <= ?lo \/ ?qq <= mf_buf ?f)%Z |- _ =>
      let E := fresh "SEPq" in assert (E : dl_sep (a + T <= lo \/ qq <= mf_buf f)%Z) by (unfold dl_sep; lia)
  end;
  try match goal with
  | FBf : (?fa + 152 <= mf_buf ?f \/ mf_buf ?f + mf_bufsize ?f <= ?fa)%Z |- _ =>
      let E := fresh "SEPf" in assert (E : dl_sep (a + T <= fa \/ fa + 152 <= mf_buf f)%Z) by (unfold dl_sep; lia)
  end.
Ltac fwx_seps :=
  leq_dedupe;
  repeat match goal with H : dl_sep _ |- _ => clear H end;
  repeat match goal with
  | H : rw_cells rsegs _ ?a [CB ?k ?bs] |- _ =>
      lazymatch k with context [length _] =>
        let T := leq_norm (Z.of_nat (cells_size [CB k bs])) in
        lazymatch goal with
        | _ : dl_sep (a + T <= _ \/ _)%Z |- _ => fail
        | _ => leq_sep a T; lazymatch goal with _ : dl_sep (a + T <= _ \/ _)%Z |- _ => idtac end
        end
      end
  end.
Ltac fwx_leqs :=
  leq_dedupe;
  repeat match goal with
  | H : bytes_at rsegs _ (mf_buf _) ?bs |- _ =>
      let N := leq_nat_size bs in let T := leq_norm (Z.of_nat N) in progress (leq_pose T)
  | H : rw_cells rsegs _ _ [CB ?k ?bs] |- _ =>
      lazymatch k with context [length _] => let T := leq_norm (Z.of_nat (cells_size [CB k bs])) in progress (leq_pose T) end
  end;
  fwx_seps.

(* [comment removed for export] *)
Ltac fwx_post FL5 :=
  lazymatch goal with PCf : file_at ?mx ?Fa ?fx |- _ =>
    let FI := fresh "FILE" in
    pose proof (file_at_p5 mx Fa fx FL5 PCf) as FI; clear PCf;
    unfold pfile5, file_cells in FI;
    cbn [tl mf_set_w mf_flags mf_rpos mf_rend mf_close mf_wend mf_wpos mf_mbz1 mf_wbase mf_read mf_write mf_seek mf_buf mf_bufsize
         mf_prev mf_next mf_fd mf_pipepid mf_lockcount mf_mode mf_lock mf_lbf mf_pad148] in FI
  end;
  repeat match goal with H : context [(?pend ++ [])%list] |- _ => rewrite app_nil_r in H end;
  repeat match goal with H : rw_cells rsegs _ _ [CB _ (skipn 0 ?r)] |- _ => change (skipn 0 r) with r in H; rewrite ?Nat.sub_0_r in H end;
  repeat match goal with H : rw_cells rsegs _ (_ + Z.of_nat (length (_ ++ _)))%Z _ |- _ => rewrite !length_app, ?length_skipn in H; cbn [length] in H end;
  repeat match goal with H : rw_cells rsegs _ _ [CB (length (skipn _ _)) _] |- _ => rewrite ?length_skipn in H end;
  repeat match goal with H : rw_cells rsegs _ ?Fa (C1 _ :: _) |- _ => progress (rewrite !length_app in H; cbn [length] in H) end;
  try match goal with H : bytes_at rsegs _ _ (?pend ++ _)%list |- _ => let n := fresh "BUF" in rename H into n end;
  try match goal with H : rw_cells rsegs _ _ [CB (length ?rest - _)%nat _] |- _ => let n := fresh "RST" in rename H into n end;
  try match goal with H : rw_cells rsegs _ _ [CB (length ?rest) ?rest] |- _ => let n := fresh "RST" in rename H into n end;
  fwx_leqs.   (* [comment removed for export] *)

(* [comment removed for export] *)
Ltac fwx_side FL5 :=
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
  | |- (_ \/ ~ In _ _)%type => right; cbn; intuition discriminate
  | |- (_ = 0%Z \/ _)%type => first [left; reflexivity | left; cbn; lia | right; split; fwx_range]
  | |- _ \/ _ => rewrite ?unsigned_lit by lia; cbn [length Z.of_nat]; rewrite ?Z.add_0_r; lia
  | |- _ => rewrite ?unsigned_lit by lia; unfold FWRITEX_STACK; cbn [length Z.of_nat]; rewrite ?length_app, ?length_skipn; cbn [length Z.of_nat]; lia
  end || match goal with |- ?G => idtac "FWXSIDE-FAIL:" G end
with fwx_range :=
  rewrite ?unsigned_lit by lia; cbn [length Z.of_nat];
  lazymatch goal with SFq : sfF _ _ _ _ _ _ _ _ ?mm |- range_ok ?mm ?a ?n =>
    first [ eapply (sfF_buf_range _ _ _ _ _ _ _ _ _ _ _ SFq); lia
          | eapply (sfF_fmt_range _ _ _ _ _ _ _ _ _ _ _ SFq); lia
          | eapply (sfF_stack_range _ _ _ _ _ _ _ _ _ _ _ SFq); lia ] end.

Section PC2D.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (lo A Fa VA : Z) (canary : word) (f : mfile) (pend rest : list byte) (ZSB : Z) (ZK : nat).
  Hypothesis FWXC : fwritex_fit_stmt.
  #[local] Notation q := (bv_unsigned sp).
  #[local] Notation B := (mf_buf f).
  #[local] Notation N := (mf_bufsize f).
  #[local] Notation wp := (mf_buf f + Z.of_nat (length pend))%Z.
  (* [comment removed for export] *)
  Hypothesis LO : (lo <= q - PC2_DEPTH)%Z.
  Hypothesis GT : (alloc_ceiling <= lo)%Z.   (* [comment removed for export] *)
  Hypothesis VLO : (q + 368 <= VA)%Z.
  Hypothesis VHI : (VA + 8 <= 2^63)%Z.
  Hypothesis ARL : (IMG_LO <= A)%Z.
  Hypothesis ART : (A + 4 <= RO_TOP)%Z.
  Hypothesis FL5 : mf_flags f = 5%Z.
  Hypothesis FWB : mf_wbase f = Z_to_bv 64 B.
  Hypothesis FWP : mf_wpos f = Z_to_bv 64 wp.
  Hypothesis FWE : mf_wend f = Z_to_bv 64 (B + N).
  Hypothesis B0 : (0 < B)%Z.
  Hypothesis BHI : (B + N < 2^47)%Z.
  Hypothesis NR : (0 <= N < 2^31)%Z.
  Hypothesis LBF : (-2^31 <= mf_lbf f < 2^31)%Z.
  Hypothesis ROOM : (Z.of_nat (length pend) + 2 <= N)%Z.
  Hypothesis PR : (Z.of_nat (length pend) + Z.of_nat (length rest) = N)%Z.
  Hypothesis FAR : (FILE_LO <= Fa /\ Fa + 152 <= FILE_HI)%Z.
  Hypothesis FB1 : (Fa + 152 <= B \/ B + N <= Fa)%Z.
  Hypothesis FB2 : (B + N <= lo \/ q + 16 <= B)%Z.
  Hypothesis FB3 : ((SBUF_LO <= B /\ B + N <= SBUF_HI) \/ kHighMemBeg_z <= B)%Z.
  Hypothesis FBV : (B + N <= VA)%Z.

  Notation FRAME1 m1 j40 := (rw_cells rsegs m1 (q + -544) (CB 40 j40 :: pc_lits sp)).
  Notation FRAMEA m1 ja1 ja2 := (rw_cells rsegs m1 (q + -432) [CB 8 ja1; CB 8 ja2]).
  Notation FRAME2 m1 j304 := (rw_cells rsegs m1 (q + -416) (CB 304 j304 :: pc_saved ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 canary)).
  Notation FILE5 m1 f1 := (rw_cells rsegs m1 Fa (pfile5 f1)).
  Notation SFF m1 := (sfF A 4 B N ZSB ZK (q - PC2_DEPTH) (q + 96) m1).

  (* [comment removed for export] *)
  Definition pfd_mid (m : word -> option byte) : machine_state -> Prop :=
    fun ms => exists (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (j40 ja1 ja2 j304 : list byte) (m' : word -> option byte),
      ms = MS (mkR (Z_to_bv 64 FWX5_RET) (Z_to_bv 64 (q + -544)) gp tp t0 t1 t2 (Z_to_bv 64 37) (Z_to_bv 64 INT_MAX)
                   (Z_to_bv 64 (A + 2)) (Z_to_bv 64 1) (Z_to_bv 64 Fa) a3 a4 a5 a6 a7
                   (Z_to_bv 64 2147483646) (Z_to_bv 64 1) (Z_to_bv 64 Fa) (Z_to_bv 64 (A + 3)) (Z_to_bv 64 1) (Z_to_bv 64 (A + 2))
                   (Z_to_bv 64 1) (Z_to_bv 64 0) (Z_to_bv 64 1) (Z_to_bv 64 1) t3 t4 t5 t6)
              F (Z_to_bv 64 FWRITEX_ENTRY) fc None m' (seg_rom rsegs)
      /\ munch [(q - PC2_DEPTH, q + 8); (Fa, Fa + 152); (wp, wp + 1)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
      /\ stk rsegs m' lo (q + -544)
      /\ FRAME1 m' j40 /\ FRAMEA m' ja1 ja2 /\ FRAME2 m' j304
      /\ file_at m' Fa (mf_set_w f (Z_to_bv 64 (wp + 1)) (Z_to_bv 64 B) (Z_to_bv 64 (B + N)))
      /\ bytes_at rsegs m' B (pend ++ [Z_to_bv 8 48])
      /\ rw_cells rsegs m' (wp + 1) [CB (length rest - 1) (skipn 1 rest)]
      /\ rw_cells rsegs m' q [C8 (Z_to_bv 64 (VA + 8))]
      /\ ssp_cells m' canary /\ SFF m'.

  #[using="FBV FB3 FB2 FB1 FAR PR ROOM LBF NR BHI B0 FWE FWP FWB FL5 ART ARL VLO GT LO FWXC Clg"] Lemma pf_pc2d_head : forall t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (m : word -> option byte) (v : word),
    a0 = Z_to_bv 64 Fa -> a1 = Z_to_bv 64 A -> a2 = sp -> a3 = Z_to_bv 64 (q + 96) -> a4 = Z_to_bv 64 (q + 264) ->
    stk rsegs m lo q -> ro_cells rsegs m A PF_pc1.FMT_D -> ssp_cells m canary ->
    file_at m Fa f -> bytes_at rsegs m B pend -> rw_cells rsegs m wp [CB (length rest) rest] ->
    rw_cells rsegs m q [C8 (Z_to_bv 64 VA)] -> va_area m VA [v] -> sx32 v = Z_to_bv 64 0 ->
    mem_inv rsegs m -> SFF m ->
    evt rsegs (pfd_mid m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PRINTF_CORE) fc None m (seg_rom rsegs)).
  Proof.
    intros until v. intros -> -> -> -> -> ST HF [SSP1 SSP2] FILE BUF RST APC VAA V0 MI SF.
    pose proof alloc_ceiling_val as CV.
    unfold RA_seql.GOT_SSP, RA_seql.SSP_GUARD, DA_Eg3i.SSP_GUARD, GLOBALS_TOP, RO_TOP, PC2_DEPTH, PRINTF_CORE, IMG_LO, IMG_HI, FILE_LO, FILE_HI, SBUF_LO, SBUF_HI, kHighMemBeg_z in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (ro_cells_bound _ _ _ _ HF) as AB. cbn [cells_size csize Nat.add] in AB.
    pose proof (bytes_at_bound _ _ _ _ BUF) as BB. pose proof (rw_CB_length _ _ _ _ _ RST) as RL.
    assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(bv_unsigned sp - 4928, bv_unsigned sp + 8); (Fa, Fa + 152); (mf_buf f + Z.of_nat (length pend), mf_buf f + Z.of_nat (length pend) + 1)]%Z m) as MU.
    pose proof (wmono_refl rsegs m) as WM.
    unfold va_area in VAA. unfold PF_pc1.FMT_D in HF.
    apply (file_at_p5 _ _ _ FL5) in FILE. unfold pfile5, file_cells in FILE. cbn [tl] in FILE.
    pose proof FWXC as FWX. unfold fwritex_fit_stmt in FWX. cbv zeta in FWX.
    assert (Q47 : (bv_unsigned sp + 112 <= 2^47)%Z) by (destruct SF as (_ & _ & _ & _ & _ & (_ & _ & _ & _ & B5 & _) & _); lia).
    rewrite <- (Z_to_bv_bv_unsigned sp) at 1.
    fwx_leqs.
    carve_frame 544%nat ST.
    do 43 zs. name_junk FR.
    (* [comment removed for export] *)
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
    (* [comment removed for export] *)
    try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_FILE); call_icpt (FWX _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ Fa f pend [] rest A lo) by (fwx_side FL5).
    fwx_post FL5. cbn [Z.of_nat].
    (* [comment removed for export] *)
    zto 0x9f078%Z. zs. br K. clear K.
    zto 0x9f9e0%Z.
    lazymatch goal with APq : rw_cells rsegs ?mx (bv_unsigned sp) [C8 (Z_to_bv 64 VA)] |- _ =>
      assert (APC' : rw_cells rsegs mx (bv_unsigned sp) [C8 (Z_to_bv 64 (VA + 8 * 0))]) by (replace (VA + 8 * 0)%Z with VA by lia; exact APq);
      clear APq; rename APC' into APC end.
    try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_APC); try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_FRA); call_lit pop_arg_int_spec by
      (first [ reflexivity | symmetry; apply Z_to_bv_bv_unsigned | exact FRA | exact VAA | assumption | lia | exact APC
             | match goal with |- ?G => idtac "POPARG-FAIL:" G; fail end ]).
    try clear FRA; try clear APC; try clear VAA; try clear ST. regrab lo VA. unfold va_area in VAA.
    zto 0x9e640%Z. rewrite !V0 in FRA. rewrite !V0. if_lit_try.
    zto 0x9e640%Z.
    change (Z.b2z (0 <? 1)) with 1%Z in *. rewrite !Z.add_0_l in *. sx. rewrite !Z.add_0_r.
    lazymatch goal with H : rw_cells rsegs _ (bv_unsigned sp + -544) _ |- _ => sxh H; replace (1 + 0)%Z with 1%Z in H by lia end.
    (* [comment removed for export] *)
    lazymatch goal with Fq : file_at _ _ ?fx |- _ => idtac | _ => idtac end.
    try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_FILE); call_icpt (FWX _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ Fa
                 (mf_set_w f (Z_to_bv 64 wp) (Z_to_bv 64 B) (Z_to_bv 64 (B + N))) pend [] rest 0x10b85%Z lo) by (fwx_side FL5).
    fwx_post FL5. cbn [Z.of_nat]. regrab lo VA.
    (* [comment removed for export] *)
    zto 0x9f678%Z.
    lazymatch goal with FR1q : rw_cells rsegs ?mx (bv_unsigned sp + -544) _ |- _ =>
      pose proof (rw_cells_read4_C8 rsegs _ _ _ 16 _ (Z_to_bv 64 (bv_unsigned sp + -544 + 16)) FR1q eq_refl ltac:(unfold wa; f_equal; lia)) as RD4 end.
    zto 0x57614%Z. clear RD4.
    lazymatch goal with FR2q : rw_cells rsegs _ (bv_unsigned sp + -416) (CB 304 ?j :: _) |- _ =>
      apply (rw_cells_split_CB rsegs _ _ [] 304 _ _ [48; 1; 255]%nat) in FR2q; [|reflexivity];
      cbn [mk_CB_cells app] in FR2q;
      apply (proj1 (rw_cells_app rsegs _ _ [_] _)) in FR2q; destruct FR2q as [FR2a FR2q];
      apply (proj1 (rw_cells_app rsegs _ _ [_] _)) in FR2q; destruct FR2q as [PAD FR2];
      cbn [cells_size csize Nat.add] in FR2a, PAD, FR2;
      replace (bv_unsigned sp + -416 + Z.of_nat 48)%Z with (bv_unsigned sp + -368)%Z in PAD by lia;
      replace (bv_unsigned sp + -416 + Z.of_nat 48 + Z.of_nat 1)%Z with (bv_unsigned sp + -367)%Z in FR2 by lia;
      name_junk FR2a; name_junk PAD; name_junk FR2 end.
    try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_PAD); lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mq _) =>
      eapply evt_cut; [ eapply memset_callv with (lo := lo) | post_call_icpt rsegs mq ] end.
    { exact PAD. } { lia. } { lia. } { lia. } { assumption. }
    { lazymatch goal with SFq : sfF _ _ _ _ _ _ _ _ _ |- _ => exact (proj1 (proj2 SFq)) end. }
    { rewrite ?unsigned_lit by lia. eassumption. } { rewrite ?unsigned_lit by lia. lia. } { assumption. }
    { rewrite ?unsigned_lit by lia. lia. }
    { right. lazymatch goal with SFq : sfF _ _ _ _ _ _ _ _ _ |- _ => eapply (sfF_stack_range _ _ _ _ _ _ _ _ _ _ _ SFq); lia end. }
    regrab lo VA.
    lazymatch goal with H : rw_cells rsegs _ (bv_unsigned sp + -368) [CB _ _] |- _ =>
      change (Z.to_nat 1) with 1%nat in H; cbn [repeat] in H; rename H into PAD1 end.
    zto 0x9e640%Z.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (SRC3 : bytes_at rsegs mx (bv_unsigned sp + -368) [Z_to_bv 8 48]) by (exact (proj2 (proj1 PAD1))) end.
    try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_FILE); try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_RST); try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_RST0); try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_RST1); call_icpt (FWX _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ Fa
                 (mf_set_w f (Z_to_bv 64 wp) (Z_to_bv 64 B) (Z_to_bv 64 (B + N))) pend [Z_to_bv 8 48] rest (bv_unsigned sp + -368)%Z lo) by (fwx_side FL5).
    fwx_post FL5. norm_small. regrab lo VA.
    (* [comment removed for export] *)
    zto 0x9e640%Z.
    try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_FILE); call_icpt (FWX _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ Fa
                 (mf_set_w f (Z_to_bv 64 (wp + 1)) (Z_to_bv 64 B) (Z_to_bv 64 (B + N))) (pend ++ [Z_to_bv 8 48]) [] (skipn 1 rest)
                 (bv_unsigned sp + -368)%Z lo) by (fwx_side FL5).
    fwx_post FL5. norm_small. regrab lo VA.
    (* [comment removed for export] *)
    zto 0x9ec60%Z.
    zto 0x9e640%Z. br K. clear K.
    zto 0x9e640%Z.
    (* [comment removed for export] *)
    apply evt_done. unfold pfd_mid, FWX5_RET, INT_MAX, PC2_DEPTH.
    lazymatch goal with FR1q : rw_cells rsegs ?mx (bv_unsigned sp + -544) _ |- _ => apply fr1_recast in FR1q end.
    lazymatch goal with FRAq : rw_cells rsegs ?mx (bv_unsigned sp + -432) _ |- _ => apply fra_recast in FRAq end.
    lazymatch goal with FR2aq : rw_cells rsegs ?mx (bv_unsigned sp + -416) [CB 48 ?ja] |- _ =>
      lazymatch goal with PADq : rw_cells rsegs mx (bv_unsigned sp + -368) [CB 1 ?jb] |- _ =>
      lazymatch goal with FR2q : rw_cells rsegs mx (bv_unsigned sp + -367) (CB 255 ?jc :: ?rest0) |- _ =>
        assert (FR2m : rw_cells rsegs mx (bv_unsigned sp + -416) ([CB 48 ja] ++ [CB 1 jb] ++ (CB 255 jc :: rest0)));
        [ apply (proj2 (rw_cells_app rsegs _ _ _ _)); split; [exact FR2aq|]; cbn [cells_size csize Nat.add];
          apply (proj2 (rw_cells_app rsegs _ _ _ _)); split; [eapply rwc_eq; [exact PADq| lia]|]; cbn [cells_size csize Nat.add];
          eapply rwc_eq; [exact FR2q| lia]
        | clear FR2aq PADq FR2q; cbn [app] in FR2m; apply cb3_recast in FR2m; cbn [Nat.add] in FR2m ] end end end.
    lazymatch goal with FIq : rw_cells rsegs ?mx Fa _ |- _ =>
      replace (mf_buf f + Z.of_nat (length pend + 1))%Z with (mf_buf f + Z.of_nat (length pend) + 1)%Z in FIq by lia;
      pose proof (file_p5_at mx Fa (mf_set_w f (Z_to_bv 64 (mf_buf f + Z.of_nat (length pend) + 1)) (Z_to_bv 64 (mf_buf f)) (Z_to_bv 64 (mf_buf f + mf_bufsize f))) FL5 FIq) as FAT end.
    lazymatch goal with APq : rw_cells rsegs ?mx (bv_unsigned sp) [C8 (Z_to_bv 64 (VA + 8 * 1))] |- _ =>
      replace (VA + 8 * 1)%Z with (VA + 8)%Z in APq by lia end.
    hot_eexists_all.
    split; [reflexivity|].
    split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
    split; [eassumption|]. split; [eassumption|]. split; [exact FR2m|]. split; [exact FAT|].
    split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
    split; [split; assumption|].
    lazymatch goal with SFq : sfF _ _ _ _ _ _ _ _ _ |- _ => exact SFq end.
  Qed.
  (* [comment removed for export] *)
  Definition pfd_ret (m : word -> option byte) : machine_state -> Prop :=
    fun ms => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
      ms = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 2) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (ret_pc ra) fc None m (seg_rom rsegs)
      /\ stk rsegs m lo q.

  #[using="FAR LO rest pend Clg"] Lemma pf_pc2d_tail : forall t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (m : word -> option byte) (j40 ja1 ja2 j304 : list byte),
    stk rsegs m lo (q + -544) -> ro_cells rsegs m A PF_pc1.FMT_D -> ssp_cells m canary -> mem_inv rsegs m ->
    FRAME1 m j40 -> FRAMEA m ja1 ja2 -> FRAME2 m j304 ->
    evt rsegs (pfd_ret m)
      (MS (mkR (Z_to_bv 64 FWX5_RET) (Z_to_bv 64 (q + -544)) gp tp t0 t1 t2 (Z_to_bv 64 37) (Z_to_bv 64 INT_MAX)
               a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 2147483646) (Z_to_bv 64 1) (Z_to_bv 64 Fa) (Z_to_bv 64 (A + 3)) (Z_to_bv 64 1) (Z_to_bv 64 (A + 2))
               (Z_to_bv 64 1) (Z_to_bv 64 0) (Z_to_bv 64 1) (Z_to_bv 64 1) t3 t4 t5 t6)
          F (Z_to_bv 64 FWX5_RET) fc None m (seg_rom rsegs)).
  Proof.
    intros until j304. intros ST HF [SSP1 SSP2] MI FR1 FRA FR2.
    pose proof alloc_ceiling_val as CV.
    unfold RA_seql.GOT_SSP, RA_seql.SSP_GUARD, DA_Eg3i.SSP_GUARD, GLOBALS_TOP, RO_TOP, PC2_DEPTH, FWX5_RET, INT_MAX, IMG_LO, IMG_HI, FILE_LO, FILE_HI, SBUF_LO, SBUF_HI, kHighMemBeg_z in *.
    unfold pc_lits in FR1. unfold pc_saved in FR2. unfold RA_seql.SSP_GUARD in FR1.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    unfold PF_pc1.FMT_D in HF. pose proof (ro_cells_bound _ _ _ _ HF) as AB. cbn [cells_size csize Nat.add] in AB.
    assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl ([] : list ivl) m) as MU. pose proof (wmono_refl rsegs m) as WM.
    zs. (* [comment removed for export] *)
    zs. br K. clear K. (* [comment removed for export] *)
    zs. zs. zs. sx. br K. clear K.
    zs. zs. zs. sx. zs. br K. clear K.
    (* [comment removed for export] *) zs. br K. clear K.
    zto 0x9f998%Z. zs. brf Kc. { exfalso. apply Kc. reflexivity. } clear Kc.
    lazymatch type of FR1 with rw_cells _ ?mq _ ?cs1 => lazymatch type of FRA with rw_cells _ _ _ ?csa => lazymatch type of FR2 with rw_cells _ _ _ ?cs2 =>
      assert (FR : rw_cells rsegs mq (bv_unsigned sp + -544) (cs1 ++ csa ++ cs2));
      [ apply (proj2 (rw_cells_app rsegs _ _ _ _)); split; [exact FR1|]; cbn [cells_size csize Nat.add];
        apply (proj2 (rw_cells_app rsegs _ _ [_;_] _)); split;
        [ eapply rwc_eq; [exact FRA| lia]
        | cbn [cells_size csize Nat.add]; eapply rwc_eq; [exact FR2| lia] ]
      | clear FR1 FRA FR2; cbn [app] in FR ] end end end.
    do 16 zs.
    release_frame FR ST (bv_unsigned sp).
    apply evt_done. unfold pfd_ret.
    hot_eexists_all.
    split; [reflexivity|]. exact ST.
  Qed.
End PC2D.
