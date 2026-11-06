From Stdlib Require Import String Ascii ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import Img0.
Import ListNotations.
Open Scope Z_scope.

Definition REC_SHAPE_OF : Z := 0x1540c.
Definition REC_SHAPE_OF_FRAME : Z := 64.
Definition G_SHAPES : Z := 0x226c8.
Definition SHAPE_LIT : Z := 0x10417.

Definition shape_rows : list (Z * string * Z) :=
  [(0x1045b, "add"%string, 0x1082b);
   (0x1060b, "worker_list"%string, 0x10384);
   (0x103c1, "instance_info"%string, 0x108b2);
   (0x10781, "supervisor_reset"%string, 0x10417);
   (0x10792, "quarantine_clear"%string, 0x10417);
   (0x10692, "policy_set"%string, 0x10417);
   (0x1059a, "pool_config"%string, 0x10417);
   (0x10705, "worker_env"%string, 0x10417);
   (0x109a1, "pin_set"%string, 0x10417);
   (0x1072e, "pin_clear"%string, 0x10417);
   (0x104ed, "lv2_worker_set"%string, 0x10417);
   (0x1064f, "pin_accept"%string, 0x10417);
   (0x1067c, "pin_layout"%string, 0x102c4);
   (0x104e2, "pin_expect"%string, 0x10417);
   (0x104fc, "chain"%string, 0x10417);
   (0x1041e, "chain_clear"%string, 0x10417);
   (0x10375, "descriptor_get"%string, 0x104b4);
   (0x109a9, "panel_get"%string, 0x104b4);
   (0x109ff, "track_info"%string, 0x10417);
   (0x10889, "remote_pages"%string, 0x103cf);
   (0x1073c, "remote_page_get"%string, 0x105ae);
   (0x104c4, "param_info"%string, 0x10502);
   (0x10972, "preset_list"%string, 0x103cf);
   (0x10713, "preset_get"%string, 0x1042a);
   (0x10638, "note_input"%string, 0x103dc);
   (0x10874, "note_on"%string, 0x10417);
   (0x1087c, "note_off"%string, 0x10417);
   (0x10323, "all_notes_off"%string, 0x10417)].

Definition str_bytes (s : string) : list byte :=
  map (fun c => Z_to_bv 8 (Z.of_N (N_of_ascii c))) (list_ascii_of_string s).

Definition g_shapes_bytes : list byte :=
  concat (map (fun r => match r with (na, _, rp) => le8 (Z_to_bv 64 na) ++ le8 (Z_to_bv 64 rp) end) shape_rows).

Definition bytes_eqb (x y : list byte) : bool :=
  if list_eq_dec Z.eq_dec (map bv_unsigned x) (map bv_unsigned y) then true else false.

Fixpoint shape_find (rows : list (Z * string * Z)) (v : list byte) : Z :=
  match rows with
  | [] => SHAPE_LIT
  | (_, nm, rp) :: rows' => if bytes_eqb (str_bytes nm) v then rp else shape_find rows' v
  end.

Definition rec_shape_of_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (v : list byte),
    mem_inv rsegs m ->
    stk rsegs m lo (bv_unsigned sp) ->
    lo + REC_SHAPE_OF_FRAME <= bv_unsigned sp ->
    bytes_at rsegs m G_SHAPES g_shapes_bytes ->
    G_SHAPES + 448 <= bv_unsigned sp - REC_SHAPE_OF_FRAME \/ bv_unsigned sp <= G_SHAPES ->
    Z.of_nat (length v) = bv_unsigned a1 ->
    (bv_unsigned a1 <= 16 ->
       bytes_at rsegs m (bv_unsigned a0) v /\
       (bv_unsigned a0 + bv_unsigned a1 <= bv_unsigned sp - REC_SHAPE_OF_FRAME \/ bv_unsigned sp <= bv_unsigned a0)) ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (shape_find shape_rows v)) a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - REC_SHAPE_OF_FRAME, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\
         mem_inv rsegs m' /\
         stk rsegs m' lo (bv_unsigned sp))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REC_SHAPE_OF) fc None m (seg_rom rsegs)).
