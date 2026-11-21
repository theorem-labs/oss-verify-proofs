(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.U Require Import Z_ikit Z_infl_defs Z_infl_c_tab Z_adler32.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.U Require Export Zg_adler32_iface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZProg ZIface InflateState InflateArms Inflate InflateFast InffastSafe AdlerModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition Z_INFFAST : Z := 0x2265c.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition ff_restored (s : inflate_state) (c : icall) (r : iregs) : Prop :=
  ic_next_in c = ir_next r /\ ic_avail_in c = ir_have r /\ ic_next_out c = ir_put r /\ ic_avail_out c = ir_left r
  /\ is_hold s = ir_hold r /\ is_bits s = ir_bits r.

(* [comment removed for export] *)
Definition ff_typed (X : ictx) (s : inflate_state) (c : icall) (r : iregs) : Prop :=
  (* [comment removed for export] *)
  ic_input c = ix_input X /\ arr_len (ic_outbuf c) = Z.of_nat (length (ix_rest0 X))
  /\ 0 <= ir_next r /\ 0 <= ir_have r /\ ir_next r + ir_have r <= arr_len (ic_input c) /\ arr_len (ic_input c) < 2^31
  /\ 0 <= ir_put r /\ 0 <= ir_left r /\ ir_put r + ir_left r <= arr_len (ic_outbuf c) /\ arr_len (ic_outbuf c) < 2^31
  /\ 0 <= ir_out r < 2^32 /\ wrap32 (ir_out r - ir_left r) <= ir_put r
  (* [comment removed for export] *)
  /\ (forall i, 0 <= arr_get (ic_input c) i < 256)
  /\ (forall i, 0 <= i < ir_put r -> 0 <= arr_get (ic_outbuf c) i < 256)
  /\ (forall i, 0 <= i < arr_len (is_window s) -> 0 <= arr_get (is_window s) i < 256)
  (* [comment removed for export] *)
  /\ 0 <= ir_bits r <= 63 /\ 0 <= ir_hold r < 2 ^ ir_bits r
  (* [comment removed for export] *)
  /\ 0 <= is_lenbits s <= 31 /\ 0 <= is_distbits s <= 31 /\ cp_ofs_ok (is_lencode s) /\ cp_ofs_ok (is_distcode s)
  /\ 0 <= is_wsize s < 2^31 /\ 0 <= is_whave s < 2^31 /\ 0 <= is_wnext s < 2^31
  /\ 0 <= is_sane s < 2^31
  /\ (is_window_blk s = None -> is_wsize s = 0) /\ (is_wsize s = 0 -> is_whave s = 0 /\ is_wnext s = 0)
  /\ (is_window_blk s <> None -> ix_hasw X = true).

(* [comment removed for export] *)
Definition inflate_fast_post (X : ictx) (s : inflate_state) (c : icall) (r : iregs)
    (ra x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 : word) : machine_state -> Prop :=
  fun ms' => exists x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m',
    ms' = MS (mkR ra (wz (bv_unsigned (ix_sp X) + -256)) (ix_gp X) (ix_tp X) x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
                 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
             (ix_F X) (ret_pc ra) (ix_fc X) None m' (seg_rom usegs)
    /\ IMEMg (fun X' _ m0 => iframe X' r m0) X (LOAD (inflate_fast (mkW s c r))) m'     (* [comment removed for export] *)
    /\ (let c2 := w_c (inflate_fast (mkW s c r)) in
        ic_input c2 = ic_input c /\ arr_len (ic_outbuf c2) = arr_len (ic_outbuf c)
        /\ ic_next_out c <= ic_next_out c2 <= arr_len (ic_outbuf c)
        /\ (forall i, 0 <= i < ic_next_out c2 -> 0 <= arr_get (ic_outbuf c2) i < 256)).

Definition inflate_fast_stmt : Prop :=
  forall (X : ictx) (s : inflate_state) (c : icall) (r : iregs)
         (ra x5 x6 x7 x8 x9 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (m : mem),
    IMEM X (mkW s c r) m -> ix_ok X -> ff_restored s c r -> ff_typed X s c r -> ff_ok s c r = true ->
    evt usegs (inflate_fast_post X s c r ra x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27)
      (MS (mkR ra (wz (bv_unsigned (ix_sp X) + -256)) (ix_gp X) (ix_tp X) x5 x6 x7 x8 x9 (wz (il_S (ix_L X))) (wz (ir_out r)) x12 x13 x14 x15 x16 x17
               x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          (ix_F X) (wz Z_INFFAST) (ix_fc X) None m (seg_rom usegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)

