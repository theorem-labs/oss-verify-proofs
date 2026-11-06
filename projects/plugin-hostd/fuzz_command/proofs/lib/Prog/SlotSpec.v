From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import Tac Arr Bytes.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Verbs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts CommandModel rec_code_declared_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require strspn_c.
Import ListNotations.
Open Scope Z_scope.

(* The Kind A runs of LLVMFuzzerTestOneInput (plain 0x14048, frame 176) between its calls, stated in the MS form of
   the Kind A contracts. The frame base is the word sp (= entry sp - 176): locals at sp (40 bytes: the code count 58,
   the code table address, &g_rec, the saved s8 and s6 of the word splitter), the struct words w at sp + 40 (text,
   copy, the pointer array, the word count), the saved registers at sp + 72. *)

Definition MASK : Z := 0x100002600.
Definition GOT_NCODES : Z := 0x22a28.
Definition GOT_CODES : Z := 0x22a30.
Definition NCODES_A : Z := 0x10be8.

Definition SAVE (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) : list cell :=
  [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Definition LOC0 (jsv : list byte) : list cell :=
  [C8 (Z_to_bv 64 58); C8 (Z_to_bv 64 REC_CODES); C8 (Z_to_bv 64 G_REC); CB 16 jsv].

(* The message header at cursor (p, n), n > 0: hdr is the min(n, 3) bytes at p (fuzz_u8 / fuzz_u16). *)
Definition hdr_n (n : Z) : Z := Z.min n 3.
Definition hbyte (hdr : list byte) (k : nat) : Z := bv_unsigned (nth k hdr (Z_to_bv 8 0)).
Definition msg_len (n : Z) (hdr : list byte) : Z :=
  Z.min (Z.min (hbyte hdr 1 + 256 * hbyte hdr 2) (n - hdr_n n)) 8192.
Definition msg_rf (hdr : list byte) : Z := hbyte hdr 0 mod 2.
Definition msg_cd (hdr : list byte) : Z := nth (Z.to_nat ((hbyte hdr 0 / 2) mod 58)) rec_codes 0.

(* The size of the pointer array of words_of: ((L0 << 2) & ~7) + 16. *)
Definition arr_size (L0 : Z) : Z := 8 * (L0 / 2) + 16.

(* 0x14048 .. jal rec_clear (0x14090), when a1 < 2^26. *)
Definition run_pro_spec : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z),
  mem_inv rsegs m ->
  stk rsegs m lo (bv_unsigned sp) -> lo + 176 <= bv_unsigned sp -> IMG_END <= lo ->
  bv_unsigned a1 < 2 ^ 26 ->
  evt rsegs (fun ms' => exists t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' jl,
      ms' = MS (mkR (Z_to_bv 64 0x14094) (Z_to_bv 64 (bv_unsigned sp - 176)) gp tp t0' t1' t2' s0 s1
                    a0' a1' a2' a3' a4' a5' a6' a7' a0 s3 s4 s5 s6 a1 s8 s9 s10 s11 t3' t4' t5' t6')
             F (Z_to_bv 64 0x1559c) fc None m' (seg_rom rsegs) /\
      munch [(bv_unsigned sp - 176, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
      rw_cells rsegs m' (bv_unsigned sp - 176) [CB 72 jl] /\
      rw_cells rsegs m' (bv_unsigned sp - 104) (SAVE ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14048) fc None m (seg_rom rsegs)).

(* 0x14048 .. ret, when a1 >= 2^26 (the size refusal: a0 = 0, the saved registers come back). *)
Definition run_big_spec : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z),
  mem_inv rsegs m ->
  stk rsegs m lo (bv_unsigned sp) -> lo + 176 <= bv_unsigned sp -> IMG_END <= lo ->
  2 ^ 26 <= bv_unsigned a1 ->
  evt rsegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7'
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom rsegs) /\
      munch [(bv_unsigned sp - 176, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m')
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14048) fc None m (seg_rom rsegs)).

(* 0x14094 (rec_clear returned) .. the loop head 0x140dc (s7 <> 0) or jal rec_clear at 0x14320 (s7 = 0): writes
   g_rec.state = g_rec.host_settings = 0, &g_rec at sp + 16, and (s7 <> 0) 58 and the code table at sp, sp + 8. *)
Definition run_init_spec : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (jsh jl : list byte),
  mem_inv rsegs m ->
  IMG_END <= bv_unsigned sp -> bv_unsigned sp + 176 <= 2 ^ 64 ->
  bytes_at rsegs m GOT_GREC (le8 (Z_to_bv 64 G_REC)) ->
  bytes_at rsegs m GOT_NCODES (le8 (Z_to_bv 64 NCODES_A)) ->
  bytes_at rsegs m GOT_CODES (le8 (Z_to_bv 64 REC_CODES)) ->
  rw_cells rsegs m (G_REC + 944) [CB 16 jsh] ->
  rw_cells rsegs m (bv_unsigned sp) [CB 40 jl] ->
  evt rsegs (fun ms' => exists t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' jl' jsv,
      munch [(bv_unsigned sp, bv_unsigned sp + 24); (G_REC + 944, G_REC + 960)] m m' /\ wmono rsegs m m' /\
      mem_inv rsegs m' /\
      rw_cells rsegs m' (G_REC + 944) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] /\
      rw_cells rsegs m' (bv_unsigned sp) [CB 40 jl'] /\
      ((bv_unsigned s7 = 0 /\
        ms' = MS (mkR (Z_to_bv 64 0x14324) sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                 F (Z_to_bv 64 0x1559c) fc None m' (seg_rom rsegs)) \/
       (bv_unsigned s7 <> 0 /\ rw_cells rsegs m' (bv_unsigned sp) (LOC0 jsv) /\
        ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7'
                      s2 s3 s4 s5 s6 s7 s8 (Z_to_bv 64 MASK) s10 (Z_to_bv 64 32) t3' t4' t5' t6')
                 F (Z_to_bv 64 0x140dc) fc None m' (seg_rom rsegs))))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14094) fc None m (seg_rom rsegs)).

(* The loop head 0x140dc (message mi at cursor (p, n), n > 0) .. jal send_message (0x14180): decodes the header,
   writes g_rec.refuse and g_rec.code, loads g_rec.state and g_rec.host_settings into s2 and s3. *)
Definition run_head_spec : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s8 s10 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (mi p n : Z) (hdr jsv jrc : list byte) (sbw hbw : word),
  mem_inv rsegs m ->
  IMG_END <= bv_unsigned sp -> bv_unsigned sp + 176 <= 2 ^ 64 ->
  0 <= mi <= 31 -> 0 < n -> 0 <= p -> p + n <= 2 ^ 64 ->
  bytes_at rsegs m p hdr -> length hdr = Z.to_nat (hdr_n n) ->
  rw_cells rsegs m (bv_unsigned sp) (LOC0 jsv) ->
  rw_cells rsegs m G_REC [CB 8 jrc] ->
  bytes_at rsegs m (G_REC + 944) (le8 sbw) -> bytes_at rsegs m (G_REC + 952) (le8 hbw) ->
  evt rsegs (fun ms' => exists t0' t1' t2' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
      ms' = MS (mkR (Z_to_bv 64 0x14184) sp gp tp t0' t1' t2'
                    (Z_to_bv 64 (p + hdr_n n)) (Z_to_bv 64 (msg_len n hdr))
                    (Z_to_bv 64 (p + hdr_n n)) (Z_to_bv 64 (msg_len n hdr)) a2' a3' a4' a5' a6' a7'
                    sbw hbw s4 s5 (Z_to_bv 64 mi) (Z_to_bv 64 n) (Z_to_bv 64 (n - hdr_n n))
                    (Z_to_bv 64 MASK) s10 (Z_to_bv 64 32) t3' t4' t5' t6')
             F (Z_to_bv 64 0x14374) fc None m' (seg_rom rsegs) /\
      munch [(G_REC, G_REC + 8)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
      rw_cells rsegs m' G_REC [C4 (Z_to_bv 64 (msg_rf hdr)); C4 (Z_to_bv 64 (msg_cd hdr))])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 mi) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 p) s3 s4 s5 s6
             (Z_to_bv 64 n) s8 (Z_to_bv 64 MASK) s10 (Z_to_bv 64 32) t3 t4 t5 t6)
        F (Z_to_bv 64 0x140dc) fc None m (seg_rom rsegs)).

(* 0x14184 (send_message returned) .. strnlen entry: a0 = s0, a1 = s1. *)
Definition run_g_strnlen_spec : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte),
  evt rsegs (fun ms' => ms' =
      MS (mkR (Z_to_bv 64 0x14190) sp gp tp t0 t1 t2 s0 s1 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
         F (Z_to_bv 64 0x20f0c) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14184) fc None m (seg_rom rsegs)).

(* 0x14190 (strnlen returned L0) .. malloc entry: s7 = L0, s5 = a0 = L0 + 1. *)
Definition run_g_m0_spec : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte),
  bv_unsigned a0 + 1 < 2 ^ 64 ->
  evt rsegs (fun ms' => ms' =
      MS (mkR (Z_to_bv 64 0x141a0) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (bv_unsigned a0 + 1)) a1 a2 a3 a4 a5 a6 a7
              s2 s3 s4 (Z_to_bv 64 (bv_unsigned a0 + 1)) s6 a0 s8 s9 s10 s11 t3 t4 t5 t6)
         F (Z_to_bv 64 0x18a0c) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14190) fc None m (seg_rom rsegs)).

(* 0x141a0 (first malloc returned text) .. malloc entry: s4 = text, text at sp + 40, a0 = s5. *)
Definition run_g_m1_spec : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (j : list byte),
  mem_inv rsegs m -> IMG_END <= bv_unsigned sp -> bv_unsigned sp + 176 <= 2 ^ 64 ->
  rw_cells rsegs m (bv_unsigned sp + 40) [CB 8 j] ->
  evt rsegs (fun ms' => exists m',
      ms' = MS (mkR (Z_to_bv 64 0x141b0) sp gp tp t0 t1 t2 s0 s1 s5 a1 a2 a3 a4 a5 a6 a7
                    s2 s3 a0 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x18a0c) fc None m' (seg_rom rsegs) /\
      munch [(bv_unsigned sp + 40, bv_unsigned sp + 48)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
      rw_cells rsegs m' (bv_unsigned sp + 40) [C8 a0])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x141a0) fc None m (seg_rom rsegs)).

(* 0x141b0 (second malloc returned copy) .. malloc entry: s5 = copy, copy at sp + 48, a0 = arr_size L0 (s7 = L0). *)
Definition run_g_m2_spec : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (j : list byte) (L0 : Z),
  mem_inv rsegs m -> IMG_END <= bv_unsigned sp -> bv_unsigned sp + 176 <= 2 ^ 64 ->
  0 <= L0 <= 8192 ->
  rw_cells rsegs m (bv_unsigned sp + 48) [CB 8 j] ->
  evt rsegs (fun ms' => exists a0' m',
      ms' = MS (mkR (Z_to_bv 64 0x141c8) sp gp tp t0 t1 t2 s0 s1 a0' a1 a2 a3 a4 a5 a6 a7
                    s2 s3 s4 a0 s6 (Z_to_bv 64 L0) s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x18a0c) fc None m' (seg_rom rsegs) /\
      a0' = Z_to_bv 64 (arr_size L0) /\
      munch [(bv_unsigned sp + 48, bv_unsigned sp + 56)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
      rw_cells rsegs m' (bv_unsigned sp + 48) [C8 a0])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 (Z_to_bv 64 L0) s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x141b0) fc None m (seg_rom rsegs)).

(* 0x141c8 (third malloc returned arr) .. jal check_reply (0x142c8): the inlined words_of. M is the message
   (len bytes at src), L0 = strnlen(src, len); text and copy hold L0 + 1 bytes, arr holds arr_size L0 bytes. At the
   end the copy holds the words of Verbs.line M, each followed by a 0, the array their addresses, w.n their count,
   s7 = s8 - s1 (the cursor count after the message), a0 = &w. *)
Definition run_words_spec : Prop :=
  forall ra sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s6 s8 s10 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo src len text copy arr : Z) (M jt jc ja jsv jw : list byte)
    (can : word),
  mem_inv rsegs m ->
  stk rsegs m lo (bv_unsigned sp) -> lo + 96 <= bv_unsigned sp -> IMG_END <= lo ->
  bv_unsigned sp + 176 <= 2 ^ 64 ->
  bytes_at rsegs m src M -> Z.of_nat (length M) = len -> len <= 8192 -> 0 <= src -> src + len <= lo ->
  0 < text -> 0 < copy -> 0 < arr ->
  rw_cells rsegs m text [CB (Z.to_nat (strnlen_res len M + 1)) jt] ->
  rw_cells rsegs m copy [CB (Z.to_nat (strnlen_res len M + 1)) jc] ->
  rw_cells rsegs m arr [CB (Z.to_nat (arr_size (strnlen_res len M))) ja] ->
  text + strnlen_res len M + 1 <= lo -> copy + strnlen_res len M + 1 <= lo -> arr + arr_size (strnlen_res len M) <= lo ->
  disjoint_from [(text, text + strnlen_res len M + 1)] copy (strnlen_res len M + 1) ->
  disjoint_from [(text, text + strnlen_res len M + 1); (copy, copy + strnlen_res len M + 1)]
    arr (arr_size (strnlen_res len M)) ->
  disjoint_from [(text, text + strnlen_res len M + 1); (copy, copy + strnlen_res len M + 1);
                 (arr, arr + arr_size (strnlen_res len M))] src len ->
  bytes_at rsegs m strspn_c.SSP_GOT (le8 (Z_to_bv 64 strspn_c.SSP_GUARD)) ->
  bytes_at rsegs m strspn_c.SSP_GUARD (le8 can) ->
  rw_cells rsegs m (bv_unsigned sp) (LOC0 jsv) ->
  rw_cells rsegs m (bv_unsigned sp + 40) [C8 (Z_to_bv 64 text); C8 (Z_to_bv 64 copy); CB 16 jw] ->
  let L0 := strnlen_res len M in
  let ws := Verbs.words (Verbs.line M) in
  evt rsegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' T C Aa wp jsv' jp,
      ms' = MS (mkR (Z_to_bv 64 0x142cc) sp gp tp t0' t1' t2' (Z_to_bv 64 src) (Z_to_bv 64 len)
                    (Z_to_bv 64 (bv_unsigned sp + 40)) a1' a2' a3' a4' a5' a6' a7'
                    s2 s3 (Z_to_bv 64 text) (Z_to_bv 64 copy) s6 (Z_to_bv 64 (bv_unsigned s8 - len)) s8
                    (Z_to_bv 64 MASK) (Z_to_bv 64 arr) (Z_to_bv 64 32) t3' t4' t5' t6')
             F (Z_to_bv 64 0x14404) fc None m' (seg_rom rsegs) /\
      munch [(text, text + L0 + 1); (copy, copy + L0 + 1); (arr, arr + arr_size L0);
             (bv_unsigned sp - 96, bv_unsigned sp + 72)] m m' /\
      wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp) /\
      rw_cells rsegs m' (bv_unsigned sp) (LOC0 jsv') /\
      rw_cells rsegs m' (bv_unsigned sp + 40)
        [C8 (Z_to_bv 64 text); C8 (Z_to_bv 64 copy); C8 (Z_to_bv 64 arr); C4 (Z_to_bv 64 (Z.of_nat (length ws)));
         CB 4 jp] /\
      rw_cells rsegs m' text [CB (Z.to_nat (L0 + 1)) T] /\
      rw_cells rsegs m' copy [CB (Z.to_nat (L0 + 1)) C] /\
      rw_cells rsegs m' arr [CB (Z.to_nat (arr_size L0)) Aa] /\
      length wp = length ws /\
      firstn (8 * length ws) Aa = concat (map (fun p => le8 (Z_to_bv 64 p)) wp) /\
      (forall k p w, nth_error wp k = Some p -> nth_error ws k = Some w ->
         copy <= p /\ p + Z.of_nat (length w) + 1 <= copy + L0 + 1 /\
         firstn (length w + 1) (skipn (Z.to_nat (p - copy)) C) = w ++ [Z_to_bv 8 0]))
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 src) (Z_to_bv 64 len) (Z_to_bv 64 arr) a1 a2 a3 a4 a5 a6 a7
             s2 s3 (Z_to_bv 64 text) (Z_to_bv 64 copy) s6 (Z_to_bv 64 (strnlen_res len M)) s8
             (Z_to_bv 64 MASK) s10 (Z_to_bv 64 32) t3 t4 t5 t6)
        F (Z_to_bv 64 0x141c8) fc None m (seg_rom rsegs)).

(* 0x142cc (check_reply returned) .. check_arity entry: a0 = &w. *)
Definition run_g_ca_spec : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte),
  bv_unsigned sp + 40 < 2 ^ 64 ->
  evt rsegs (fun ms' => ms' =
      MS (mkR (Z_to_bv 64 0x142d4) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (bv_unsigned sp + 40)) a1 a2 a3 a4 a5 a6 a7
              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
         F (Z_to_bv 64 0x14514) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x142cc) fc None m (seg_rom rsegs)).

(* 0x142d4 (check_arity returned) .. check_words entry: a0 = &w. *)
Definition run_g_cw_spec : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte),
  bv_unsigned sp + 40 < 2 ^ 64 ->
  evt rsegs (fun ms' => ms' =
      MS (mkR (Z_to_bv 64 0x142dc) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (bv_unsigned sp + 40)) a1 a2 a3 a4 a5 a6 a7
              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
         F (Z_to_bv 64 0x14980) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x142d4) fc None m (seg_rom rsegs)).

(* 0x142dc (check_words returned) .. check_refusal entry: a0 = s2. *)
Definition run_g_cr_spec : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte),
  evt rsegs (fun ms' => ms' =
      MS (mkR (Z_to_bv 64 0x142e4) sp gp tp t0 t1 t2 s0 s1 s2 a1 a2 a3 a4 a5 a6 a7
              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
         F (Z_to_bv 64 0x14c18) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x142dc) fc None m (seg_rom rsegs)).

(* 0x142e4 (check_refusal returned) .. check_round_trip entry: a0 = &w, a1 = s2, a2 = s3. *)
Definition run_g_crt_spec : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte),
  bv_unsigned sp + 40 < 2 ^ 64 ->
  evt rsegs (fun ms' => ms' =
      MS (mkR (Z_to_bv 64 0x142f4) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (bv_unsigned sp + 40)) s2 s3 a3 a4 a5 a6 a7
              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
         F (Z_to_bv 64 0x14c78) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x142e4) fc None m (seg_rom rsegs)).

(* 0x142f4, 0x142fc, 0x14304 .. free entry with a0 = s4, s5, s10 (the three frees of words_free). *)
Definition run_g_f1_spec : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte),
  evt rsegs (fun ms' => ms' =
      MS (mkR (Z_to_bv 64 0x142fc) sp gp tp t0 t1 t2 s0 s1 s4 a1 a2 a3 a4 a5 a6 a7
              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
         F (Z_to_bv 64 0x188cc) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x142f4) fc None m (seg_rom rsegs)).

Definition run_g_f2_spec : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte),
  evt rsegs (fun ms' => ms' =
      MS (mkR (Z_to_bv 64 0x14304) sp gp tp t0 t1 t2 s0 s1 s5 a1 a2 a3 a4 a5 a6 a7
              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
         F (Z_to_bv 64 0x188cc) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x142fc) fc None m (seg_rom rsegs)).

Definition run_g_f3_spec : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte),
  evt rsegs (fun ms' => ms' =
      MS (mkR (Z_to_bv 64 0x1430c) sp gp tp t0 t1 t2 s0 s1 s10 a1 a2 a3 a4 a5 a6 a7
              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
         F (Z_to_bv 64 0x188cc) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14304) fc None m (seg_rom rsegs)).

(* 0x1430c (the third free returned) .. the next loop head (s7 <> 0 and s6 < 31: s2 = s0 + s1, a0 = s6 + 1) or
   jal rec_clear at 0x14320. *)
Definition run_tail_spec : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte),
  bv_unsigned s6 <= 31 -> bv_unsigned s0 + bv_unsigned s1 < 2 ^ 64 ->
  evt rsegs (fun ms' =>
      (bv_unsigned s7 <> 0 /\ bv_unsigned s6 < 31 /\
       ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (bv_unsigned s6 + 1)) (Z_to_bv 64 31) a2 a3 a4 a5 a6 a7
                     (Z_to_bv 64 (bv_unsigned s0 + bv_unsigned s1)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x140dc) fc None m (seg_rom rsegs)) \/
      ((bv_unsigned s7 = 0 \/ bv_unsigned s6 = 31) /\
       exists a0' a1' s2',
       ms' = MS (mkR (Z_to_bv 64 0x14324) sp gp tp t0 t1 t2 s0 s1 a0' a1' a2 a3 a4 a5 a6 a7
                     s2' s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x1559c) fc None m (seg_rom rsegs)))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1430c) fc None m (seg_rom rsegs)).

(* 0x14324 (the second rec_clear returned) .. ret: g_quitting = 0 through its GOT slot, a0 = 0, the saved
   registers come back, sp = sp + 176. *)
Definition run_epi_spec : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (ra0 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : word) (jq : list byte),
  mem_inv rsegs m -> IMG_END <= bv_unsigned sp -> bv_unsigned sp + 176 <= 2 ^ 64 ->
  bytes_at rsegs m GOT_GQUIT (le8 (Z_to_bv 64 G_QUIT)) ->
  rw_cells rsegs m G_QUIT [CB 4 jq] ->
  rw_cells rsegs m (bv_unsigned sp + 72) (SAVE ra0 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11) ->
  evt rsegs (fun ms' => exists a0' m',
      ms' = MS (mkR ra0 (Z_to_bv 64 (bv_unsigned sp + 176)) gp tp t0 t1 t2 x0 x1 a0' a1 a2 a3 a4 a5 a6 a7
                    x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 t3 t4 t5 t6)
             F (ret_pc ra0) fc None m' (seg_rom rsegs) /\
      a0' = Z_to_bv 64 0 /\
      munch [(G_QUIT, G_QUIT + 4)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
      rw_cells rsegs m' G_QUIT [C4 (Z_to_bv 64 0)])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14324) fc None m (seg_rom rsegs)).
