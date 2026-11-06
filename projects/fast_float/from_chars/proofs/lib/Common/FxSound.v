(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore.

Module FxGlue.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import FxLin FxCore.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope bv_scope.

Definition mks (fr : bvmap 5 word) (fc : bv 32) (regs : bvmap 5 word) (pc : word) (rv : option word)
    (mem rom : word -> option byte) : machine_state :=
  {| ms_regs := regs; ms_fregs := fr; ms_pc_val := pc; ms_svc_pending := None; ms_resv := rv; ms_fcsr := fc;
     ms_mem := mem; ms_rom := rom |}.

Lemma mks_eta : forall ms, ms_svc_pending ms = None ->
  ms = mks (ms_fregs ms) (ms_fcsr ms) (ms_regs ms) (ms_pc_val ms) (ms_resv ms) (ms_mem ms) (ms_rom ms).
Proof. intros [r f p sv rv fc m ro] H; cbn in *; subst; reflexivity. Qed.

(* [comment removed for export] *)
Definition rupd (regs : bvmap 5 word) (rd : reg) (v : word) : bvmap 5 word :=
  if bv_eqb rd 0 then regs else regupd regs rd v.
(* [comment removed for export] *)
Definition ival (a : word) (rv : option word) : option word :=
  match rv with Some r => if Z.eqb (bv_unsigned r) (bv_unsigned a) then None else Some r | None => None end.

Definition frm_zero (f : bv 32) : Prop := Z.land (Z.shiftr (bv_unsigned f) 5) 7 = 0%Z.

Definition st_word (sz : msize) (v : word) : Z :=
  match sz with
  | SZ1 => bv_unsigned (bv_extract 0 8 v) | SZ2 => bv_unsigned (bv_extract 0 16 v)
  | SZ4 => bv_unsigned (low32 v) | SZ8 => bv_unsigned v
  end.
(* [comment removed for export] *)
Definition amo_word (op : amoop) (wd : awidth) (old src : word) : word :=
  match wd with
  | AW => zext 64 (amo_val op (bv_extract 0 32 old) (low32 src))
  | AD => amo_val op old src
  end.

Ltac gpipe Hfetch Hecall Hdecode :=
  unfold RiscvSemantics.step, RiscvSemantics.step_accesses;
  cbn [ms_pc ms_pc_val mks];
  rewrite Hfetch;
  cbv beta iota;
  unfold RiscvSemantics.drop_access_report, RiscvSemantics.decode_exec_accesses;
  rewrite Hecall;
  cbv beta iota;
  rewrite Hdecode;
  cbv beta iota zeta delta
    [RiscvSemantics.interp_eff_accesses
     RiscvSemantics.width_bytes RiscvSemantics.width_bytesZ
     Sem.exec Sem.load_val Sem.store_val
     Sem.rget Sem.rset Sem.with_regs Sem.with_pc Sem.with_resv
     Sem.fget Sem.fset Sem.with_fregs Sem.with_fcsr Sem.fread Sem.fwrite
     Sem.accrue Sem.resolve_rm Sem.frm_of
     Sem.inval_resv Sem.w0 Sem.w1
     Sem.c_regs Sem.c_fregs Sem.c_pc Sem.c_fcsr Sem.c_resv
     RiscvSemantics.access_value RiscvSemantics.drop_access_report
     ms_regs ms_fregs ms_fcsr ms_pc_val ms_svc_pending ms_resv ms_mem ms_rom mks];
  rewrite ?bv_eqb0_is_x0.

Ltac gfin := unfold rupd, regupd, getr, ival; rewrite ?bv_eqb0_is_x0;
  repeat match goal with
         | |- context [is_x0 ?r] => destruct (is_x0 r); cbv beta iota
         | |- context [match ?rv with Some _ => _ | None => _ end] => destruct rv; cbv beta iota
         | |- context [if ?b then _ else _] => destruct b; cbv beta iota
         end; reflexivity.

Section G.
Variable segs : list Segment.
Variables (fr : bvmap 5 word) (fc : bv 32) (regs : bvmap 5 word) (pc : word) (rv : option word) (mem rom : word -> option byte) (w : bv 32).
Hypothesis Hfetch : fetch_word segs pc = Some w.
Hypothesis Hecall : is_ecall w = false.

#[using="Hfetch Hecall"] Lemma g_opimm : forall op rd rs (imm : bv 12), decode_any w = Some (OpImm op rd rs imm, 4%Z) ->
  RiscvSemantics.step segs (mks fr fc regs pc rv mem rom) =
  MachineOk (mks fr fc (rupd regs rd (alu64 op (getr regs rs) (sext 64 imm))) (pc + Z_to_bv 64 4) rv mem rom).
Proof. LiaFast.lf_pins (fun (Hfetch Hecall : LiaFast.U) => LiaFast.u0). intros op rd rs imm Hd. gpipe Hfetch Hecall Hd. gfin. Qed.

#[using="Hfetch Hecall"] Lemma g_shiftimm : forall op rd rs (sh : bv 6), decode_any w = Some (ShiftImm op rd rs sh, 4%Z) ->
  RiscvSemantics.step segs (mks fr fc regs pc rv mem rom) =
  MachineOk (mks fr fc (rupd regs rd (alu64 op (getr regs rs) (zext 64 sh))) (pc + Z_to_bv 64 4) rv mem rom).
Proof. LiaFast.lf_pins (fun (Hfetch Hecall : LiaFast.U) => LiaFast.u0). intros op rd rs sh Hd. gpipe Hfetch Hecall Hd. gfin. Qed.

#[using="Hfetch Hecall"] Lemma g_op : forall op rd rs1 rs2, decode_any w = Some (Op op rd rs1 rs2, 4%Z) ->
  RiscvSemantics.step segs (mks fr fc regs pc rv mem rom) =
  MachineOk (mks fr fc (rupd regs rd (alu64 op (getr regs rs1) (getr regs rs2))) (pc + Z_to_bv 64 4) rv mem rom).
Proof. LiaFast.lf_pins (fun (Hfetch Hecall : LiaFast.U) => LiaFast.u0). intros op rd rs1 rs2 Hd. gpipe Hfetch Hecall Hd. gfin. Qed.

#[using="Hfetch Hecall"] Lemma g_opimm32 : forall rd rs (imm : bv 12), decode_any w = Some (OpImm32 rd rs imm, 4%Z) ->
  RiscvSemantics.step segs (mks fr fc regs pc rv mem rom) =
  MachineOk (mks fr fc (rupd regs rd (sext 64 (alu32 ALU_ADD (low32 (getr regs rs)) (sext 32 imm)))) (pc + Z_to_bv 64 4) rv mem rom).
Proof. LiaFast.lf_pins (fun (Hfetch Hecall : LiaFast.U) => LiaFast.u0). intros rd rs imm Hd. gpipe Hfetch Hecall Hd. gfin. Qed.

#[using="Hfetch Hecall"] Lemma g_shiftimm32 : forall op rd rs (sh : bv 5), decode_any w = Some (ShiftImm32 op rd rs sh, 4%Z) ->
  RiscvSemantics.step segs (mks fr fc regs pc rv mem rom) =
  MachineOk (mks fr fc (rupd regs rd (sext 64 (alu32 op (low32 (getr regs rs)) (zext 32 sh)))) (pc + Z_to_bv 64 4) rv mem rom).
Proof. LiaFast.lf_pins (fun (Hfetch Hecall : LiaFast.U) => LiaFast.u0). intros op rd rs sh Hd. gpipe Hfetch Hecall Hd. gfin. Qed.

#[using="Hfetch Hecall"] Lemma g_op32 : forall op rd rs1 rs2, decode_any w = Some (Op32 op rd rs1 rs2, 4%Z) ->
  RiscvSemantics.step segs (mks fr fc regs pc rv mem rom) =
  MachineOk (mks fr fc (rupd regs rd (sext 64 (alu32 op (low32 (getr regs rs1)) (low32 (getr regs rs2))))) (pc + Z_to_bv 64 4) rv mem rom).
Proof. LiaFast.lf_pins (fun (Hfetch Hecall : LiaFast.U) => LiaFast.u0). intros op rd rs1 rs2 Hd. gpipe Hfetch Hecall Hd. gfin. Qed.

#[using="Hfetch Hecall"] Lemma g_mul : forall op rd rs1 rs2, decode_any w = Some (Mul op rd rs1 rs2, 4%Z) ->
  RiscvSemantics.step segs (mks fr fc regs pc rv mem rom) =
  MachineOk (mks fr fc (rupd regs rd (mul_div op (getr regs rs1) (getr regs rs2))) (pc + Z_to_bv 64 4) rv mem rom).
Proof. LiaFast.lf_pins (fun (Hfetch Hecall : LiaFast.U) => LiaFast.u0). intros op rd rs1 rs2 Hd. gpipe Hfetch Hecall Hd. gfin. Qed.

#[using="Hfetch Hecall"] Lemma g_mul32 : forall op rd rs1 rs2, decode_any w = Some (Mul32 op rd rs1 rs2, 4%Z) ->
  RiscvSemantics.step segs (mks fr fc regs pc rv mem rom) =
  MachineOk (mks fr fc (rupd regs rd (sext 64 (mul_div op (low32 (getr regs rs1)) (low32 (getr regs rs2))))) (pc + Z_to_bv 64 4) rv mem rom).
Proof. LiaFast.lf_pins (fun (Hfetch Hecall : LiaFast.U) => LiaFast.u0). intros op rd rs1 rs2 Hd. gpipe Hfetch Hecall Hd. gfin. Qed.

#[using="Hfetch Hecall"] Lemma g_lui : forall rd (imm : bv 20), decode_any w = Some (Lui rd imm, 4%Z) ->
  RiscvSemantics.step segs (mks fr fc regs pc rv mem rom) =
  MachineOk (mks fr fc (rupd regs rd (sext 64 (bv_concat 32 imm (Z_to_bv 12 0)))) (pc + Z_to_bv 64 4) rv mem rom).
Proof. LiaFast.lf_pins (fun (Hfetch Hecall : LiaFast.U) => LiaFast.u0). intros rd imm Hd. gpipe Hfetch Hecall Hd. gfin. Qed.

#[using="Hfetch Hecall"] Lemma g_auipc : forall rd (imm : bv 20), decode_any w = Some (Auipc rd imm, 4%Z) ->
  RiscvSemantics.step segs (mks fr fc regs pc rv mem rom) =
  MachineOk (mks fr fc (rupd regs rd (pc + sext 64 (bv_concat 32 imm (Z_to_bv 12 0)))) (pc + Z_to_bv 64 4) rv mem rom).
Proof. LiaFast.lf_pins (fun (Hfetch Hecall : LiaFast.U) => LiaFast.u0). intros rd imm Hd. gpipe Hfetch Hecall Hd. gfin. Qed.

#[using="Hfetch Hecall"] Lemma g_jal : forall rd (imm : bv 21), decode_any w = Some (Jal rd imm, 4%Z) ->
  RiscvSemantics.step segs (mks fr fc regs pc rv mem rom) =
  MachineOk (mks fr fc (rupd regs rd (pc + Z_to_bv 64 4)) (pc + sext 64 imm) rv mem rom).
Proof. LiaFast.lf_pins (fun (Hfetch Hecall : LiaFast.U) => LiaFast.u0). intros rd imm Hd. gpipe Hfetch Hecall Hd. gfin. Qed.

#[using="Hfetch Hecall"] Lemma g_jalr : forall rd rs (imm : bv 12), decode_any w = Some (Jalr rd rs imm, 4%Z) ->
  RiscvSemantics.step segs (mks fr fc regs pc rv mem rom) =
  MachineOk (mks fr fc (rupd regs rd (pc + Z_to_bv 64 4)) (bv_and (getr regs rs + sext 64 imm) (bv_not w1)) rv mem rom).
Proof. LiaFast.lf_pins (fun (Hfetch Hecall : LiaFast.U) => LiaFast.u0). intros rd rs imm Hd. gpipe Hfetch Hecall Hd. gfin. Qed.

#[using="Hfetch Hecall"] Lemma g_branch : forall c rs1 rs2 (imm : bv 13), decode_any w = Some (Branch c rs1 rs2 imm, 4%Z) ->
  RiscvSemantics.step segs (mks fr fc regs pc rv mem rom) =
  MachineOk (mks fr fc regs (if branch_taken c (getr regs rs1) (getr regs rs2) then pc + sext 64 imm else pc + Z_to_bv 64 4) rv mem rom).
Proof. LiaFast.lf_pins (fun (Hfetch Hecall : LiaFast.U) => LiaFast.u0). intros c rs1 rs2 imm Hd. gpipe Hfetch Hecall Hd. gfin. Qed.

#[using="Hfetch Hecall"] Lemma g_fence : forall i, decode_any w = Some (i, 4%Z) ->
  (match i with Fence _ _ _ _ _ | FenceI _ _ _ => True | _ => False end) ->
  RiscvSemantics.step segs (mks fr fc regs pc rv mem rom) = MachineOk (mks fr fc regs (pc + Z_to_bv 64 4) rv mem rom).
Proof. LiaFast.lf_pins (fun (Hfetch Hecall : LiaFast.U) => LiaFast.u0). intros i Hd Hi. destruct i; try contradiction; gpipe Hfetch Hecall Hd; reflexivity. Qed.

#[using="Hfetch Hecall"] Lemma g_load : forall sz sg rd rs (imm : bv 12) bs, decode_any w = Some (Load sz sg rd rs imm, 4%Z) ->
  ov_read_bytes segs mem (getr regs rs + sext 64 imm) (nbytes sz) = Some bs ->
  RiscvSemantics.step segs (mks fr fc regs pc rv mem rom) =
  MachineOk (mks fr fc (rupd regs rd (ld_word sz sg bs)) (pc + Z_to_bv 64 4) rv mem rom).
Proof. LiaFast.lf_pins (fun (Hfetch Hecall : LiaFast.U) => LiaFast.u0).
  intros sz sg rd rs imm bs Hd Hr. unfold getr in *. rewrite ?bv_eqb0_is_x0 in *.
  gpipe Hfetch Hecall Hd. destruct sz; cbn [nbytes] in Hr; rewrite Hr; cbv beta iota; unfold ld_word; destruct sg; gfin.
Qed.

#[using="Hfetch Hecall"] Lemma g_store : forall sz rs1 rs2 (imm : bv 12), decode_any w = Some (Store sz rs1 rs2 imm, 4%Z) ->
  store_ok segs mem (getr regs rs1 + sext 64 imm) (nbytes sz) = true ->
  RiscvSemantics.step segs (mks fr fc regs pc rv mem rom) =
  MachineOk (mks fr fc regs (pc + Z_to_bv 64 4) (ival (getr regs rs1 + sext 64 imm) rv)
               (write_to_mem mem (getr regs rs1 + sext 64 imm) (Z_to_le_bytes (nbytes sz) (st_word sz (getr regs rs2)))) rom).
Proof. LiaFast.lf_pins (fun (Hfetch Hecall : LiaFast.U) => LiaFast.u0).
  intros sz rs1 rs2 imm Hd Hok. unfold getr in *. rewrite ?bv_eqb0_is_x0 in *.
  gpipe Hfetch Hecall Hd. destruct sz; cbn [nbytes] in Hok; rewrite Hok; cbv beta iota; gfin.
Qed.

#[using="Hfetch Hecall"] Lemma g_lr : forall wd aq rl rd rs bs, decode_any w = Some (Lr wd aq rl rd rs, 4%Z) ->
  amo_aligned wd (getr regs rs) = true ->
  ov_read_bytes segs mem (getr regs rs) (nbytes (amo_sz wd)) = Some bs ->
  RiscvSemantics.step segs (mks fr fc regs pc rv mem rom) =
  MachineOk (mks fr fc (rupd regs rd (ld_word (amo_sz wd) (amo_sg wd) bs)) (pc + Z_to_bv 64 4) (Some (getr regs rs)) mem rom).
Proof. LiaFast.lf_pins (fun (Hfetch Hecall : LiaFast.U) => LiaFast.u0).
  intros wd aq rl rd rs bs Hd Hal Hr. unfold getr in *. rewrite ?bv_eqb0_is_x0 in *.
  gpipe Hfetch Hecall Hd. rewrite Hal. cbv beta iota delta [negb].
  destruct wd; cbn [nbytes amo_sz] in Hr; cbv beta iota; rewrite Hr; cbv beta iota; unfold ld_word; cbn [amo_sg]; gfin.
Qed.

#[using="Hfetch Hecall"] Lemma g_sc_ok : forall wd aq rl rd rs1 rs2 r, decode_any w = Some (Sc wd aq rl rd rs1 rs2, 4%Z) ->
  amo_aligned wd (getr regs rs1) = true ->
  rv = Some r -> bv_unsigned r = bv_unsigned (getr regs rs1) ->
  store_ok segs mem (getr regs rs1) (nbytes (amo_sz wd)) = true ->
  RiscvSemantics.step segs (mks fr fc regs pc rv mem rom) =
  MachineOk (mks fr fc (rupd regs rd (Z_to_bv 64 0)) (pc + Z_to_bv 64 4) None
               (write_to_mem mem (getr regs rs1) (Z_to_le_bytes (nbytes (amo_sz wd)) (st_word (amo_sz wd) (getr regs rs2)))) rom).
Proof. LiaFast.lf_pins (fun (Hfetch Hecall : LiaFast.U) => LiaFast.u0).
  intros wd aq rl rd rs1 rs2 r Hd Hal Hrv Hr Hok. subst rv. unfold getr in *. rewrite ?bv_eqb0_is_x0 in *.
  gpipe Hfetch Hecall Hd. rewrite Hal. cbv beta iota delta [negb]. rewrite Hr, Z.eqb_refl. cbv beta iota.
  destruct wd; cbn [nbytes amo_sz st_word] in Hok |- *; cbv beta iota; rewrite Hok; cbv beta iota; gfin.
Qed.

#[using="Hfetch Hecall"] Lemma g_sc_fail : forall wd aq rl rd rs1 rs2, decode_any w = Some (Sc wd aq rl rd rs1 rs2, 4%Z) ->
  amo_aligned wd (getr regs rs1) = true ->
  match rv with Some r => Z.eqb (bv_unsigned r) (bv_unsigned (getr regs rs1)) = false | None => True end ->
  RiscvSemantics.step segs (mks fr fc regs pc rv mem rom) =
  MachineOk (mks fr fc (rupd regs rd (Z_to_bv 64 1)) (pc + Z_to_bv 64 4) None mem rom).
Proof. LiaFast.lf_pins (fun (Hfetch Hecall : LiaFast.U) => LiaFast.u0).
  intros wd aq rl rd rs1 rs2 Hd Hal Hrv. unfold getr in *. rewrite ?bv_eqb0_is_x0 in *.
  gpipe Hfetch Hecall Hd. rewrite Hal. cbv beta iota delta [negb].
  destruct rv as [r|]; [rewrite Hrv|]; cbv beta iota; gfin.
Qed.

#[using="Hfetch Hecall"] Lemma g_amo : forall op wd aq rl rd rs1 rs2 bs, decode_any w = Some (Amo op wd aq rl rd rs1 rs2, 4%Z) ->
  amo_aligned wd (getr regs rs1) = true ->
  ov_read_bytes segs mem (getr regs rs1) (nbytes (amo_sz wd)) = Some bs ->
  store_ok segs mem (getr regs rs1) (nbytes (amo_sz wd)) = true ->
  RiscvSemantics.step segs (mks fr fc regs pc rv mem rom) =
  MachineOk (mks fr fc (rupd regs rd (ld_word (amo_sz wd) (amo_sg wd) bs)) (pc + Z_to_bv 64 4) (ival (getr regs rs1) rv)
               (write_to_mem mem (getr regs rs1)
                  (Z_to_le_bytes (nbytes (amo_sz wd)) (st_word (amo_sz wd) (amo_word op wd (ld_word (amo_sz wd) (amo_sg wd) bs) (getr regs rs2))))) rom).
Proof. LiaFast.lf_pins (fun (Hfetch Hecall : LiaFast.U) => LiaFast.u0).
  intros op wd aq rl rd rs1 rs2 bs Hd Hal Hr Hok. unfold getr in *. rewrite ?bv_eqb0_is_x0 in *.
  gpipe Hfetch Hecall Hd. rewrite Hal. cbv beta iota delta [negb].
  destruct wd; cbn [nbytes amo_sz] in Hr, Hok; cbv beta iota; rewrite Hr; cbv beta iota; rewrite Hok; cbv beta iota.
  - unfold ld_word, amo_word, st_word; cbn [amo_sg amo_sz nbytes].
    (* [comment removed for export] *)
    assert (E1 : forall x : bv 32, low32 (zext 64 x) = x).
    { intros x. apply bv_eq. unfold low32, zext. rewrite bv_extract_unsigned, bv_zero_extend_unsigned by lia.
      rewrite Z.shiftr_0_r. apply bv_wrap_small. apply (bv_unsigned_in_range _ x). }
    assert (E2 : forall x : bv 32, bv_extract 0 32 (sext 64 x) = x).
    { intros x. apply bv_eq. unfold sext. rewrite bv_extract_unsigned, bv_sign_extend_unsigned, Z.shiftr_0_r.
      rewrite bv_wrap_bv_wrap by lia. unfold bv_signed, bv_swrap, bv_wrap.
      rewrite Zminus_mod_idemp_l, Z.add_simpl_r. apply Z.mod_small. apply (bv_unsigned_in_range _ x). }
    rewrite E1, E2. gfin.
  - unfold ld_word, amo_word, st_word; cbn [amo_sg amo_sz nbytes]. gfin.
Qed.

#[using="Hfetch Hecall"] Lemma g_fload : forall fmt rd rs (imm : bv 12) bs, decode_any w = Some (FLoad fmt rd rs imm, 4%Z) ->
  ov_read_bytes segs mem (getr regs rs + sext 64 imm) (nbytes (fsz fmt)) = Some bs ->
  exists fr', RiscvSemantics.step segs (mks fr fc regs pc rv mem rom) = MachineOk (mks fr' fc regs (pc + Z_to_bv 64 4) rv mem rom).
Proof. LiaFast.lf_pins (fun (Hfetch Hecall : LiaFast.U) => LiaFast.u0).
  intros fmt rd rs imm bs Hd Hr. unfold getr in *. rewrite ?bv_eqb0_is_x0 in *.
  destruct fmt; cbn [nbytes fsz] in Hr; (eexists; gpipe Hfetch Hecall Hd; rewrite Hr; cbv beta iota; reflexivity).
Qed.

Definition fst_word (fmt : ffmt) (v : word) : Z := match fmt with FMT_S => bv_unsigned (low32 v) | FMT_D => bv_unsigned v end.

#[using="Hfetch Hecall"] Lemma g_fstore : forall fmt rs1 rs2 (imm : bv 12), decode_any w = Some (FStore fmt rs1 rs2 imm, 4%Z) ->
  store_ok segs mem (getr regs rs1 + sext 64 imm) (nbytes (fsz fmt)) = true ->
  RiscvSemantics.step segs (mks fr fc regs pc rv mem rom) =
  MachineOk (mks fr fc regs (pc + Z_to_bv 64 4) (ival (getr regs rs1 + sext 64 imm) rv)
               (write_to_mem mem (getr regs rs1 + sext 64 imm) (Z_to_le_bytes (nbytes (fsz fmt)) (fst_word fmt (reg_get fr rs2)))) rom).
Proof. LiaFast.lf_pins (fun (Hfetch Hecall : LiaFast.U) => LiaFast.u0).
  intros fmt rs1 rs2 imm Hd Hok. unfold getr in *. rewrite ?bv_eqb0_is_x0 in *.
  gpipe Hfetch Hecall Hd. destruct fmt; cbn [nbytes fsz] in Hok; rewrite Hok; cbv beta iota; gfin.
Qed.

#[using="Type"] Lemma fflags_bits_range : forall fl, (0 <= fflags_bits fl < 32)%Z.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros [nv dz of uf nx]. unfold fflags_bits. cbn [fl_nx fl_uf fl_of fl_dz fl_nv].
  destruct nv, dz, of, uf, nx; vm_compute; split; congruence.
Qed.

#[using="pc mem rom"] Lemma frm_zero_accrue : forall (f : bv 32) fl, frm_zero f -> frm_zero (Z_to_bv 32 (Z.lor (bv_unsigned f) (fflags_bits fl))).
Proof. LiaFast.lf_pins (fun (pc mem rom : LiaFast.U) => LiaFast.u0).
  intros f fl Hf. unfold frm_zero in *. pose proof (fflags_bits_range fl) as Hb.
  pose proof (bv_unsigned_in_range _ f) as Hr. unfold bv_modulus in Hr. change (2 ^ Z.of_N 32)%Z with 4294967296%Z in Hr.
  assert (Hl : (0 <= Z.lor (bv_unsigned f) (fflags_bits fl) < 4294967296)%Z).
  { split; [apply Z.lor_nonneg; lia|].
    change 4294967296%Z with (2 ^ 32)%Z. apply Z_bounded_by_bits; [lia | apply Z.lor_nonneg; lia |].
    intros k Hk. rewrite Z.lor_spec.
    rewrite (Z_testbit_high 32 (bv_unsigned f) k) by (change (2 ^ 32)%Z with 4294967296%Z; lia).
    rewrite (Z_testbit_high 32 (fflags_bits fl) k) by (change (2 ^ 32)%Z with 4294967296%Z; lia). reflexivity. }
  rewrite Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus; change (2 ^ Z.of_N 32)%Z with 4294967296%Z; exact Hl).
  rewrite Z.shiftr_lor. rewrite (Z.shiftr_div_pow2 (fflags_bits fl) 5) by lia.
  rewrite (Z.div_small (fflags_bits fl) (2 ^ 5)) by (change (2 ^ 5)%Z with 32%Z; lia). rewrite Z.lor_0_r. exact Hf.
Qed.

#[using="pc mem rom"] Lemma resolve_ok : forall (rm : bv 3) (f : bv 32), frm_zero f -> (Z.leb (bv_unsigned rm) 4 || Z.eqb (bv_unsigned rm) 7)%bool = true ->
  exists md, rmode_of_field (bv_unsigned rm) (Z.land (Z.shiftr (bv_unsigned f) 5) 7) = Some md.
Proof. LiaFast.lf_pins (fun (pc mem rom : LiaFast.U) => LiaFast.u0).
  intros rm f Hf Hrm. unfold rmode_of_field. rewrite Hf. apply orb_prop in Hrm as [H|H].
  - apply Z.leb_le in H. pose proof (bv_unsigned_in_range _ rm) as Hr.
    destruct (Z.eqb_spec (bv_unsigned rm) 7) as [E|NE]; [lia|].
    unfold rmode_of_Z.
    destruct (Z.eqb_spec (bv_unsigned rm) 0); [eexists; reflexivity|].
    destruct (Z.eqb_spec (bv_unsigned rm) 1); [eexists; reflexivity|].
    destruct (Z.eqb_spec (bv_unsigned rm) 2); [eexists; reflexivity|].
    destruct (Z.eqb_spec (bv_unsigned rm) 3); [eexists; reflexivity|].
    destruct (Z.eqb_spec (bv_unsigned rm) 4); [eexists; reflexivity|].
    exfalso; lia.
  - apply Z.eqb_eq in H. rewrite H. exists RNE. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Hfetch Hecall"] Lemma g_fop : forall i, decode_any w = Some (i, 4%Z) -> frm_zero fc ->
  (match i with
   | Fmv FMV_F_X _ _ _ | Fsgnj _ _ _ _ _ => True
   | Fari _ _ _ _ _ rm => (Z.leb (bv_unsigned rm) 4 || Z.eqb (bv_unsigned rm) 7)%bool = true
   | Fcvt dst _ _ _ rm => (dst = FC_S \/ dst = FC_D) /\ (Z.leb (bv_unsigned rm) 4 || Z.eqb (bv_unsigned rm) 7)%bool = true
   | _ => False end) ->
  exists fr' fc', frm_zero fc' /\
    RiscvSemantics.step segs (mks fr fc regs pc rv mem rom) = MachineOk (mks fr' fc' regs (pc + Z_to_bv 64 4) rv mem rom).
Proof. LiaFast.lf_pins (fun (Hfetch Hecall : LiaFast.U) => LiaFast.u0).
  intros i Hd Hz Hi.
  assert (Hacc : forall fl, frm_zero (Z_to_bv 32 (Z.lor (bv_unsigned fc) (fflags_bits fl)))) by (intros fl; apply frm_zero_accrue; exact Hz).
  destruct i; try contradiction.
  - (* [comment removed for export] *)
    destruct (resolve_ok rm fc Hz Hi) as [md Hmd].
    gpipe Hfetch Hecall Hd. rewrite Hmd. cbv beta iota.
    repeat match goal with |- context [let '(_, _) := ?p in _] => destruct p as [?v ?fl]; cbv beta iota end.
    destruct fmt; cbv beta iota; (eexists _, _; split; [apply Hacc | reflexivity]).
  - (* [comment removed for export] *)
    destruct fmt; (eexists _, _; split; [exact Hz|]; gpipe Hfetch Hecall Hd; reflexivity).
  - (* [comment removed for export] *)
    destruct Hi as [Hdst Hrm]. destruct (resolve_ok rm fc Hz Hrm) as [md Hmd].
    gpipe Hfetch Hecall Hd. rewrite Hmd. cbv beta iota. unfold getr; rewrite ?bv_eqb0_is_x0.
    destruct Hdst as [-> | ->]; destruct src; cbv beta iota;
      repeat match goal with |- context [let '(_, _) := ?p in _] => destruct p as [?v ?fl]; cbv beta iota end;
      try (destruct (is_x0 rs1); cbv beta iota);
      repeat match goal with |- context [let '(_, _) := ?p in _] => destruct p as [?v ?fl]; cbv beta iota end;
      (eexists _, _; split; [ | reflexivity ]; first [apply Hacc | exact Hz]).
  - (* [comment removed for export] *)
    destruct dir; [contradiction|]. destruct fmt; (eexists _, _; split; [exact Hz|]; gpipe Hfetch Hecall Hd; reflexivity).
Qed.

(* [comment removed for export] *)
#[using="Hfetch Hecall"] Lemma g_fint : forall i rd, decode_any w = Some (i, 4%Z) -> frm_zero fc ->
  (match i with
   | Fmv FMV_X_F _ rd' _ => rd' = rd
   | Fcmp _ _ rd' _ _ => rd' = rd
   | Fcvt dst src rd' _ rm => rd' = rd /\ dst <> FC_S /\ dst <> FC_D /\ (src = FC_S \/ src = FC_D) /\
                             (Z.leb (bv_unsigned rm) 4 || Z.eqb (bv_unsigned rm) 7)%bool = true
   | _ => False end) ->
  exists (v : word) fc', frm_zero fc' /\
    (match i with Fcmp _ _ _ _ _ => v = Z_to_bv 64 0 \/ v = Z_to_bv 64 1 | _ => True end) /\
    RiscvSemantics.step segs (mks fr fc regs pc rv mem rom) = MachineOk (mks fr fc' (rupd regs rd v) (pc + Z_to_bv 64 4) rv mem rom).
Proof. LiaFast.lf_pins (fun (Hfetch Hecall : LiaFast.U) => LiaFast.u0).
  intros i rd Hd Hz Hi.
  assert (Hacc : forall fl, frm_zero (Z_to_bv 32 (Z.lor (bv_unsigned fc) (fflags_bits fl)))) by (intros fl; apply frm_zero_accrue; exact Hz).
  destruct i; try contradiction.
  - (* [comment removed for export] *)
    subst rd. gpipe Hfetch Hecall Hd.
    repeat match goal with |- context [let '(_, _) := ?p in _] => destruct p as [?v ?fl]; cbv beta iota end.
    exists (if v then Z_to_bv 64 1 else Z_to_bv 64 0); eexists; split; [apply Hacc|]. split; [destruct v; [right|left]; reflexivity|].
    gfin.
  - (* [comment removed for export] *)
    destruct Hi as (-> & Hd1 & Hd2 & Hsrc & Hrm). destruct (resolve_ok rm fc Hz Hrm) as [md Hmd].
    gpipe Hfetch Hecall Hd. rewrite Hmd. cbv beta iota.
    destruct dst; try (exfalso; congruence); destruct Hsrc as [-> | ->]; cbv beta iota;
      repeat match goal with |- context [let '(_, _) := ?p in _] => destruct p as [?v ?fl]; cbv beta iota end;
      cbn [Z.eqb Pos.eqb]; cbv beta iota;
      (eexists _, _; split; [apply Hacc | split; [exact I | gfin]]).
  - (* [comment removed for export] *)
    destruct dir; [|contradiction]. subst rd.
    destruct fmt; (eexists _, _; split; [exact Hz | split; [exact I|]]; gpipe Hfetch Hecall Hd; gfin).
Qed.
End G.
End FxGlue.

Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound.FxGlue.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition regs_ok (E : valu) (R : tree lin) (regs : bvmap 5 word) : Prop :=
  forall r : reg, getr regs r = lden E (rget R (rkey r)).

Lemma rkey_1 : forall r : reg, rkey r = xH <-> r = 0%bv.
Proof.
  intros r. unfold rkey, bv_key. pose proof (bv_unsigned_in_range _ r) as Hr. split.
  - intros H. apply bv_eq. change (bv_unsigned (0 : reg)) with 0.
    destruct (bv_unsigned r) eqn:E; [reflexivity | | lia]. cbn in H. lia.
  - intros ->. reflexivity.
Qed.

Lemma lden_lc0 : forall E, lden E lc0 = Z_to_bv 64 0.
Proof. reflexivity. Qed.

Lemma rget_rset_same : forall R k l, k <> xH -> rget (rset R k l) k = l.
Proof. intros R k l Hk. destruct k as [p|p|]; [| |congruence]; cbn [rset rget]; rewrite tget_tset_same; reflexivity. Qed.
Lemma rget_rset_other : forall R k k' l, k' <> k -> rget (rset R k l) k' = rget R k'.
Proof.
  intros R k k' l Hne. unfold rset, rget.
  destruct k as [p|p|]; try reflexivity;
    (destruct k' as [q|q|]; try reflexivity; rewrite tget_tset_other by congruence; reflexivity).
Qed.

Lemma regs_ok_upd : forall E R regs (rd : reg) l v,
  regs_ok E R regs -> lden E l = v ->
  regs_ok E (rset R (rkey rd) l) (if bv_eqb rd 0 then regs else regupd regs rd v).
Proof.
  intros E R regs rd l v HR Hv r.
  destruct (bv_eqb rd 0) eqn:Hrd.
  - assert (Hrd0 : rd = 0%bv) by (apply bv_eq; unfold bv_eqb in Hrd; apply Z.eqb_eq in Hrd; exact Hrd).
    subst rd. unfold rset. change (rkey 0%bv) with xH. apply HR.
  - assert (Hne : rd <> 0%bv) by (intros ->; discriminate).
    assert (Hk : rkey rd <> xH) by (intros H; apply Hne, rkey_1, H).
    destruct (decide (r = rd)) as [->|Hr].
    + rewrite getr_same by exact Hne. rewrite rget_rset_same by exact Hk. exact (eq_sym Hv).
    + rewrite getr_other by exact Hr. rewrite HR. rewrite rget_rset_other; [reflexivity|].
      intros Heq. apply Hr. apply bv_key_inj. exact Heq.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition agree (n : positive) (E E' : valu) : Prop := forall x, (x < n)%positive -> E x = E' x.
Lemma agree_refl : forall n E, agree n E E. Proof. intros n E x _. reflexivity. Qed.
Lemma agree_trans : forall n E1 E2 E3, agree n E1 E2 -> agree n E2 E3 -> agree n E1 E3.
Proof. intros n E1 E2 E3 H1 H2 x Hx. rewrite H1, H2 by exact Hx. reflexivity. Qed.
Lemma agree_mono : forall n n' E E', (n <= n')%positive -> agree n' E E' -> agree n E E'.
Proof. intros n n' E E' Hn H x Hx. apply H. lia. Qed.

Definition upd (E : valu) (x : positive) (v : word) : valu := fun y => if Pos.eqb y x then v else E y.
Lemma agree_upd : forall n E v, agree n E (upd E n v).
Proof. intros n E v x Hx. unfold upd. destruct (Pos.eqb_spec x n); [lia | reflexivity]. Qed.

Section WithSegs.
Variable segs : list Segment.

Definition rd1 (m : word -> option byte) (a : word) : option byte :=
  match m a with Some b => Some b | None => seg_rom segs a end.

Definition bden (E : valu) (v : bval) : byte :=
  match v with
  | BK b => Z_to_bv 8 b
  | BV l j => Z_to_bv 8 (Z.shiftr (bv_unsigned (lden E l)) (8 * j))
  end.

(* [comment removed for export] *)
Definition rsz (E : valu) (R : region) : Z := bv_unsigned (lden E (rg_size R)).

(* [comment removed for export] *)
Definition rg_ok (E : valu) (m : word -> option byte) (R : region) : Prop :=
  let A := bv_unsigned (lden E (rg_base R)) in
  0 <= rsz E R /\ A + rsz E R <= two64 /\
  (forall i, 0 <= i < rsz E R ->
     match rg_kind R with
     | RW => rd1 m (Z_to_bv 64 (A + i)) <> None /\ wview segs m (Z_to_bv 64 (A + i)) <> None
     | RO => m (Z_to_bv 64 (A + i)) = None /\ seg_rom segs (Z_to_bv 64 (A + i)) <> None
     | RZ => (rd1 m (Z_to_bv 64 (A + i)) <> None /\ wview segs m (Z_to_bv 64 (A + i)) <> None) /\
             (tget (okey i) (rg_cont R) = None -> rd1 m (Z_to_bv 64 (A + i)) = Some (Z_to_bv 8 0))
     | RI => (rd1 m (Z_to_bv 64 (A + i)) <> None /\ wview segs m (Z_to_bv 64 (A + i)) <> None) /\
             (tget (okey i) (rg_cont R) = None -> rd1 m (Z_to_bv 64 (A + i)) = seg_rom segs (Z_to_bv 64 (A + i)))
     | RT => rd1 m (Z_to_bv 64 (A + i)) <> None
     end) /\
  (forall p v, tget p (rg_cont R) = Some v -> Zpos p - 1 < rsz E R /\ rd1 m (Z_to_bv 64 (A + (Zpos p - 1))) = Some (bden E v)).

(* [comment removed for export] *)
Definition rg_disj (E : valu) (R1 R2 : region) : Prop :=
  let A1 := bv_unsigned (lden E (rg_base R1)) in
  let A2 := bv_unsigned (lden E (rg_base R2)) in
  A1 + rsz E R1 <= A2 \/ A2 + rsz E R2 <= A1.
Fixpoint rgs_disj (E : valu) (rgs : list region) : Prop :=
  match rgs with [] => True | R :: rs => Forall (rg_disj E R) rs /\ rgs_disj E rs end.

Definition fact_ok (E : valu) (f : fact) : Prop :=
  match f with
  | FCond c a b tk => branch_taken c (lden E a) (lden E b) = tk
  | FRange l lo hi => lo <= bv_unsigned (lden E l) <= hi
  | FMod l k r => bv_unsigned (lden E l) mod 2 ^ k = r
  | FBits l m v => Z.land (bv_unsigned (lden E l)) m = v
  | FByte x v j => bv_unsigned (lden E x) = Z.land (Z.shiftr (bv_unsigned (lden E v)) (8 * j)) 255
  | FBytes x bs => forall i, (i < length bs)%nat ->
      Z.land (Z.shiftr (bv_unsigned (lden E x)) (8 * Z.of_nat i)) 255 =
      Z.land (Z.shiftr (bv_unsigned (lden E (fst (nth i bs (lconst 0, 0))))) (8 * snd (nth i bs (lconst 0, 0)))) 255
  end.

(* [comment removed for export] *)
Definition rsv_ok (E : valu) (r : rsv) (v : option word) : Prop :=
  match r with RNone => v = None | RAt l => v = Some (lden E l) | RUnk => True end.

Definition sden0 (E : valu) (s : sst) (ms : machine_state) : Prop :=
  ms_pc_val ms = Z_to_bv 64 (s_pc s) /\ ms_svc_pending ms = None /\ rsv_ok E (s_resv s) (ms_resv ms) /\
  regs_ok E (s_regs s) (ms_regs ms) /\ Forall (rg_ok E (ms_mem ms)) (s_rgs s) /\ rgs_disj E (s_rgs s) /\
  Forall (fact_ok E) (s_facts s) /\ frm_zero (ms_fcsr ms).

Definition sden (E : valu) (s : sst) (ms : machine_state) : Prop :=
  forall E', agree (s_next s) E E' -> sden0 E' s ms.

#[using="Type"] Lemma sden_0 : forall E s ms, sden E s ms -> sden0 E s ms.
Proof. LiaFast.lf_pins LiaFast.u0. intros E s ms H. apply H, agree_refl. Qed.

(* [comment removed for export] *)
Definition img_ok (img : tree Z) : Prop :=
  forall p w, tget p img = Some w -> forall j, 0 <= j < 8 ->
    seg_rom segs (Z_to_bv 64 (8 * (Zpos p - 1) + j)) = Some (Z_to_bv 8 (Z.land (Z.shiftr w (8 * j)) 255)).

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition tbl_ok (t : tree xi) : Prop :=
  forall pc x, tlookup t pc = x -> x <> XOther -> x <> XEcall ->
    exists w i, fetch_word segs (Z_to_bv 64 pc) = Some w /\ is_ecall w = false /\
                decode_any w = Some (i, 4%Z) /\ xlate pc i = x.

Definition ent_ok (pc : Z) (x : xi) : Prop :=
  x <> XOther -> x <> XEcall ->
    exists w i, fetch_word segs (Z_to_bv 64 pc) = Some w /\ is_ecall w = false /\
                decode_any w = Some (i, 4%Z) /\ xlate pc i = x.

#[using="Type"] Lemma xentry_ok : forall pc, ent_ok pc (xentry segs pc).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros pc H1 H2. unfold xentry in *.
  destruct (fetch_word segs (Z_to_bv 64 pc)) as [w|] eqn:Hf; [|congruence].
  destruct (is_ecall w) eqn:He; [congruence|].
  destruct (decode_any w) as [[i sz]|] eqn:Hd; [|congruence].
  destruct (Z.eqb sz 4) eqn:Hsz; [|congruence]. apply Z.eqb_eq in Hsz. subst sz.
  exists w, i. repeat split; first [reflexivity | assumption].
Qed.

#[using="Type"] Lemma tget_empty : forall {A} p, @tget A p TEmpty = None.
Proof. LiaFast.lf_pins LiaFast.u0. intros A p; destruct p; reflexivity. Qed.

Definition ttbl_ok (t : tree xi) : Prop := forall p x, tget p t = Some x -> ent_ok (Zpos p) x.

#[using="Type"] Lemma ttbl_ok_tbl_ok : forall t, ttbl_ok t -> tbl_ok t.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros t Ht pc x Hx H1 H2. unfold tlookup in Hx. destruct pc as [|p|p]; try (subst; congruence).
  destruct (tget p t) as [x'|] eqn:E; [|subst; congruence]. subst x'. exact (Ht p x E H1 H2).
Qed.

#[using="Type"] Lemma mk_tbl_acc_ok : forall n pc t, ttbl_ok t -> ttbl_ok (mk_tbl_acc segs n pc t).
Proof. LiaFast.lf_pins LiaFast.u0.
  induction n as [|n IH]; intros pc t Ht; cbn [mk_tbl_acc]; [exact Ht|].
  apply IH. destruct pc as [|p|p]; try exact Ht.
  intros q x Hq. destruct (Pos.eq_dec q p) as [->|Hne].
  - rewrite tget_tset_same in Hq. injection Hq as <-. apply xentry_ok.
  - rewrite tget_tset_other in Hq by congruence. exact (Ht q x Hq).
Qed.

#[using="Type"] Lemma mk_tbl_ranges_ok : forall rs, tbl_ok (mk_tbl_ranges segs rs).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros rs. apply ttbl_ok_tbl_ok. unfold mk_tbl_ranges.
  assert (H0 : ttbl_ok TEmpty) by (intros p x H; rewrite tget_empty in H; discriminate).
  revert H0. generalize (@TEmpty xi) as t. induction rs as [|[lo n] rs IH]; intros t Ht; cbn [mk_tbl_ranges_acc]; [exact Ht|].
  apply IH. apply mk_tbl_acc_ok. exact Ht.
Qed.

#[using="Type"] Lemma mk_tbl_ok : forall lo n, tbl_ok (mk_tbl segs lo n).
Proof. LiaFast.lf_pins LiaFast.u0. intros lo n. apply ttbl_ok_tbl_ok. apply mk_tbl_acc_ok. intros p x H; rewrite tget_empty in H; discriminate. Qed.

End WithSegs.
