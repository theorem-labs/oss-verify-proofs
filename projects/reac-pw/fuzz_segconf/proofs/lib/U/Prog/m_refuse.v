(** m_refuse (UBSan build, 0x14f30, 248 bytes): proof of [m_refuse_contract] (U/Prog/m_refuse_c.v) from its
    callee's contract [snprintf_m_contract] (U/Prog/snprintf_m_c.v). Written new; the plain walk is Prog/m_refuse.v,
    and this file differs from it in the image, the addresses and the UBSan checks.

    Code (the UBSan build's disassembly):
      0x14f30-0x14f38  frame of 16: ra at sp+8, s0 at sp+0
      0x14f3c andi a2,a0,3; 0x14f40 bnez -> trap (c 16-aligned)
      0x14f44-0x14f50  a4 = line, s0 = c + 0x2008; 0x14f54 lw a1,0x3a4(s0) (n_kept)
      0x14f5c blt 7,a1 -> 0x15008 (n_kept = 8: only refused++); 0x14f60 blez a4 -> 0x14fb0
      0x14f64-0x14fac  line > 0: bgeu n_kept,9 -> trap; a5 = c + 0x200c + 112 n_kept, `not`/bltu -> trap (no wrap,
                       c + 9236 <= 2^64); snprintf(a5, 112, "%s:%d: " (0x10338), reading, line); j 0x14ff8
      0x14fb0-0x14ff4  line = 0: bltu 8,n_kept -> trap; the same slot and wrap check; snprintf(a4, 112, "%s: "
                       (0x108c4), reading)
      0x14ff8-0x15004  n_kept++ (addiw; blt -> trap on signed overflow, n_kept <= 7)
      0x15008-0x15010  refused++      0x15014-0x15020  epilogue      0x15024 unimp (every trap)

    The walk steps over [mr_snprintf], the callee at m_refuse's two call shapes, stated below in
    printf_facts_c.v's own vocabulary (pf_arg_ok's slack form for the %s argument, pf_img_free's form --
    seg_spec.blk_noimg -- for the destination, seg_env.ret_post_fp for the post), and [mr_snprintf_of_m] proves it
    from snprintf_m_contract through Spec/SegPrintfBridge.v (pm_addr_line, pm_addr, pargs_addr_line). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Image ZBridge FP Arr.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.Lib Require ITree.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.Spec Require Prelim FmtFp.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.GX Require Printf_model G_printf_core_common.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require SegPrintfBridge.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import seg_env m_refuse_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import printf_facts_c printf_model_c snprintf_c snprintf_m_c.
Import ListNotations.
Open Scope Z_scope.

(** * The callee at m_refuse's two call shapes *)

Definition MR_SNPRINTF : Z := 0x19a14.
Definition MR_FMT_AL : Z := 0x10338.   (* "%s:%d: " = SegModel.F_addr_line *)
Definition MR_FMT_A : Z := 0x108c4.    (* "%s: "    = SegModel.F_addr *)

(** A byte of a printf %s argument: nonzero and below 256 (printf_facts_c.pf_arg_ok's [Forall]). *)
Definition pbyte (x : Z) : Prop := 0 < x < 256.

(** The %s argument at r, exactly printf_facts_c.pf_arg_ok's [APtr] case: the bytes of s, its NUL and the slack up
    to the next 8-byte boundary present, that whole span apart from the stack [lo, S) and from the destination
    [D, D + n). NOT seg_spec.va_arg_ok's `length s + 8` form: m_refuse's premise only gives apart c (9236 + 4) lo sp
    and c->reading may end at the last byte of the 9236-byte block, so the `+ 8` form is not derivable here. *)
Definition mr_str (m : word -> option byte) (S lo D n r : Z) (s : list Z) : Prop :=
  Forall pbyte s /\
  exists slack : list byte,
    bytes_at rsegs m r (zb (s ++ [0]) ++ slack) /\
    (- (r + Z.of_nat (length s) + 1)) mod 8 <= Z.of_nat (length slack) /\
    0 < r /\
    (r + Z.of_nat (length s) + 1 + Z.of_nat (length slack) <= lo \/ S <= r) /\
    (r + Z.of_nat (length s) + 1 + Z.of_nat (length slack) <= D \/ D + n <= r).

(** What the call gives back (seg_env.ret_post_fp): a0 = snprintf_r f args, the text snprintf_s n f args and its
    NUL at D, and only the stack region [lo, sp) and that text written. *)
Definition mr_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
    (m : word -> option byte) (lo D n : Z) (f : list Z) (args : list arg) : machine_state -> Prop :=
  ret_post_fp ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F (snprintf_r f args) m
    [(lo, bv_unsigned sp); (D, D + Z.of_nat (length (snprintf_s n f args)) + 1)] lo
    (fun m' => bytes_at rsegs m' D (zb (snprintf_s n f args) ++ [ZERO])).

(** snprintf(D, n, fmt, ...) at the two shapes m_refuse uses: a2 = 0x10338 with the string in a3 and the int in a4,
    or a2 = 0x108c4 with the string in a3. *)
Definition mr_snprintf : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (junk : list byte)
         (rd : list Z) (line : Z) (f : list Z) (args : list arg),
    (f = F_addr_line /\ args = [AS rd; AI line] /\ bv_unsigned a2 = MR_FMT_AL /\
       bv_unsigned a4 = line /\ 0 <= line < 2 ^ 31
     \/ f = F_addr /\ args = [AS rd] /\ bv_unsigned a2 = MR_FMT_A) ->
    bytes_at rsegs m (bv_unsigned a2) (zb (f ++ [0])) ->
    mr_str m (bv_unsigned sp) lo (bv_unsigned a0) (bv_unsigned a1) (bv_unsigned a3) rd ->
    Z.of_nat (length rd) <= 65535 ->
    rw_cells rsegs m (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a1)) junk] ->
    1 <= bv_unsigned a1 < 2 ^ 31 ->
    0 < bv_unsigned a0 ->
    (bv_unsigned a0 + bv_unsigned a1 <= lo \/ bv_unsigned sp <= bv_unsigned a0) ->
    blk_noimg rsegs (bv_unsigned a0) (bv_unsigned a1) ->
    stk rsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - PRINTF_K ->
    printf_env m fc lo (bv_unsigned sp) -> mem_inv rsegs m ->
    evt rsegs
      (mr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m lo (bv_unsigned a0) (bv_unsigned a1) f args)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 MR_SNPRINTF) fc None m (seg_rom rsegs)).

(** * Generic facts: lists, bytes, printf texts, encodings *)

Lemma Forall_firstn_gen : forall {A} (P : A -> Prop) n (l : list A), Forall P l -> Forall P (firstn n l).
Proof.
  intros A P n. induction n as [|n IH]; intros l H; [constructor|].
  destruct l as [|x l]; [constructor|]. inversion H; subst. cbn [firstn]. constructor; auto.
Qed.

Lemma pbyte_nulfree : forall l, Forall pbyte l -> ~ In 0 l.
Proof. intros l H Hin. rewrite Forall_forall in H. specialize (H 0 Hin). unfold pbyte in H. lia. Qed.

Lemma zs_app : forall l1 l2, zs (l1 ++ l2) = zs l1 ++ zs l2.
Proof. intros. unfold zs. apply map_app. Qed.
Lemma zb_app : forall l1 l2, zb (l1 ++ l2) = zb l1 ++ zb l2.
Proof. intros. unfold zb. apply map_app. Qed.
Lemma length_zb : forall l, length (zb l) = length l.
Proof. intros. unfold zb. apply length_map. Qed.
Lemma pf_bytes_zb : forall l, pf_bytes l = zb l.
Proof. reflexivity. Qed.

Lemma zs_zb : forall l, Forall pbyte l -> zs (zb l) = l.
Proof.
  unfold zs, zb. induction l as [|x l IH]; intros H; [reflexivity|]. inversion H as [|? ? Hx Hl]; subst.
  cbn [map]. f_equal; [|exact (IH Hl)].
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256%Z. apply Z.mod_small.
  unfold pbyte in Hx. lia.
Qed.

Lemma cut_nul_pbyte : forall s, Forall pbyte s -> Forall pbyte (cut_nul s).
Proof.
  induction s as [|x s IH]; intros H; cbn [cut_nul]; [constructor|].
  inversion H; subst. destruct (x =? 0); [constructor | constructor; auto].
Qed.

Lemma cut_nul_len : forall l, (length (cut_nul l) <= length l)%nat.
Proof.
  induction l as [|x l IH]; cbn [cut_nul length]; [lia|].
  destruct (x =? 0); cbn [length]; lia.
Qed.

Lemma dec_go_pbyte : forall fu n acc, Forall pbyte acc -> Forall pbyte (dec_go fu n acc).
Proof.
  induction fu as [|fu IH]; intros n acc H; cbn [dec_go]; [exact H|].
  assert (Hd : Forall pbyte ((48 + n mod 10) :: acc)).
  { constructor; [|exact H]. unfold pbyte. pose proof (Z.mod_pos_bound n 10). lia. }
  destruct (n <? 10); [exact Hd | apply IH, Hd].
Qed.

Lemma dec_pbyte : forall z, Forall pbyte (dec z).
Proof.
  intros z. unfold dec. destruct (z <? 0); [constructor; [unfold pbyte; lia|]|]; apply dec_go_pbyte; constructor.
Qed.

Lemma dec_go_len : forall fu n acc, (length (dec_go fu n acc) <= fu + length acc)%nat.
Proof.
  induction fu as [|fu IH]; intros n acc; cbn [dec_go]; [lia|].
  destruct (n <? 10); cbn [length]; [lia|].
  specialize (IH (n / 10) ((48 + n mod 10) :: acc)). cbn [length] in IH. lia.
Qed.

Lemma dec_len : forall z, (length (dec z) <= 21)%nat.
Proof.
  intros z. unfold dec. pose proof (dec_go_len 20 z (@nil Z)) as H1.
  pose proof (dec_go_len 20 (- z) (@nil Z)) as H2. cbn [length] in H1, H2.
  destruct (z <? 0); cbn [length]; lia.
Qed.

Definition argp (a : arg) : Prop := match a with AS s => Forall pbyte s | AI _ => True end.

Lemma arg_s_pbyte : forall x, argp x -> Forall pbyte (arg_s x).
Proof. intros [s|z] H; cbn [arg_s argp] in *; [apply cut_nul_pbyte, H | constructor]. Qed.

Lemma fmt_pbyte_n : forall n f a, (length f <= n)%nat -> Forall pbyte f -> Forall argp a -> Forall pbyte (fmt f a).
Proof.
  induction n as [|n IH]; intros f a Hl Hf Ha.
  - destruct f; [constructor | cbn in Hl; lia].
  - destruct f as [|cc f1]; [constructor|]. inversion Hf as [|? ? Hc Hf1]; subst. cbn [length] in Hl.
    cbn [fmt].
    match goal with |- context [if negb ?b then _ else _] => destruct (negb b) end; cbv beta iota.
    + constructor; [exact Hc | apply IH; auto; lia].
    + destruct f1 as [|c1 f2]; cbv beta iota; [constructor|].
      inversion Hf1 as [|? ? Hc1 Hf2]; subst. cbn [length] in Hl.
      destruct (c1 =? 115); cbv beta iota.
      { destruct a as [|x a']; cbv beta iota; [constructor|]. inversion Ha; subst.
        apply Forall_app; split; [apply arg_s_pbyte; assumption | apply IH; auto; lia]. }
      destruct ((c1 =? 100) || (c1 =? 117)); cbv beta iota.
      { destruct a as [|x a']; cbv beta iota; [constructor|]. inversion Ha; subst.
        apply Forall_app; split; [apply dec_pbyte | apply IH; auto; lia]. }
      destruct (c1 =? 122); cbv beta iota.
      { destruct f2 as [|c2 f3]; cbv beta iota; [constructor|].
        inversion Hf2 as [|? ? _ Hf3]; subst. cbn [length] in Hl.
        destruct (c2 =? 117); cbv beta iota; [|constructor].
        destruct a as [|x a']; cbv beta iota; [constructor|]. inversion Ha; subst.
        apply Forall_app; split; [apply dec_pbyte | apply IH; auto; lia]. }
      destruct (c1 =? 46); cbv beta iota; [|constructor].
      destruct f2 as [|d1 [|d2 [|c3 f4]]]; cbv beta iota; try constructor.
      inversion Hf2 as [|? ? _ Hf2a]; subst. inversion Hf2a as [|? ? _ Hf2b]; subst.
      inversion Hf2b as [|? ? _ Hf4]; subst. cbn [length] in Hl.
      destruct (isdigit d1 && isdigit d2 && (c3 =? 115)); cbv beta iota; [|constructor].
      destruct a as [|x a']; cbv beta iota; [constructor|]. inversion Ha; subst.
      apply Forall_app; split; [apply Forall_firstn_gen, arg_s_pbyte; assumption | apply IH; auto; lia].
Qed.

Lemma snprintf_len : forall f a, (length (snprintf_s 112 f a) < 112)%nat.
Proof. intros f a. unfold snprintf_s. rewrite length_firstn. lia. Qed.

(** How long a text can get: one byte per literal, at most [arglen] per conversion. (The texts themselves are not
    computed: [vm_compute] on [dec line] with a symbolic line unfolds its 20 steps into both branches each time.) *)
Definition arglen (a : arg) : nat := match a with AS s => (length s + 21)%nat | AI _ => 21%nat end.
Fixpoint arglens (l : list arg) : nat := match l with [] => 0%nat | x :: l' => (arglen x + arglens l')%nat end.

Lemma arg_s_len : forall x, (length (arg_s x) <= arglen x)%nat.
Proof.
  intros [s|z]; cbn [arg_s arglen]; [pose proof (cut_nul_len s); lia | cbn [length]; lia].
Qed.

Lemma fmt_len_n : forall n f a, (length f <= n)%nat -> (length (fmt f a) <= length f + arglens a)%nat.
Proof.
  induction n as [|n IH]; intros f a Hl.
  - destruct f; [cbn [fmt length]; lia | cbn [length] in Hl; lia].
  - destruct f as [|cc f1]; [cbn [fmt length]; lia|]. cbn [length] in Hl.
    cbn [fmt].
    match goal with |- context [if negb ?b then _ else _] => destruct (negb b) end; cbv beta iota.
    + cbn [length]. specialize (IH f1 a ltac:(lia)). lia.
    + destruct f1 as [|c1 f2]; cbv beta iota; [cbn [fmt length]; lia|].
      cbn [length] in Hl. cbn [length].
      destruct (c1 =? 115); cbv beta iota.
      { destruct a as [|x a']; cbv beta iota; [cbn [fmt length]; lia|].
        rewrite length_app. pose proof (arg_s_len x). specialize (IH f2 a' ltac:(lia)).
        cbn [arglens]. lia. }
      destruct ((c1 =? 100) || (c1 =? 117)); cbv beta iota.
      { destruct a as [|x a']; cbv beta iota; [cbn [fmt length]; lia|].
        rewrite length_app. pose proof (dec_len (arg_i x)). specialize (IH f2 a' ltac:(lia)).
        cbn [arglens]. destruct x; cbn [arglen]; lia. }
      destruct (c1 =? 122); cbv beta iota.
      { destruct f2 as [|c2 f3]; cbv beta iota; [cbn [fmt length]; lia|].
        cbn [length] in Hl |- *.
        destruct (c2 =? 117); cbv beta iota; [|cbn [fmt length]; lia].
        destruct a as [|x a']; cbv beta iota; [cbn [fmt length]; lia|].
        rewrite length_app. pose proof (dec_len (arg_i x)). specialize (IH f3 a' ltac:(lia)).
        cbn [arglens]. destruct x; cbn [arglen]; lia. }
      destruct (c1 =? 46); cbv beta iota; [|cbn [fmt length]; lia].
      destruct f2 as [|d1 [|d2 [|c3 f4]]]; cbv beta iota; try (cbn [fmt length]; lia).
      cbn [length] in Hl |- *.
      destruct (isdigit d1 && isdigit d2 && (c3 =? 115)); cbv beta iota; [|cbn [fmt length]; lia].
      destruct a as [|x a']; cbv beta iota; [cbn [fmt length]; lia|].
      rewrite length_app, length_firstn. pose proof (arg_s_len x). specialize (IH f4 a' ltac:(lia)).
      cbn [arglens]. lia.
Qed.

Lemma fmt_len : forall f a, Z.of_nat (length (fmt f a)) <= Z.of_nat (length f) + Z.of_nat (arglens a).
Proof. intros f a. pose proof (fmt_len_n (length f) f a (le_n _)). lia. Qed.

Lemma fmt_al_pbyte : forall r line, Forall pbyte r -> Forall pbyte (fmt F_addr_line [AS r; AI line]).
Proof.
  intros r line H. apply fmt_pbyte_n with (n := length F_addr_line); [lia| |].
  - apply Forall_forall. intros x Hx. unfold pbyte. vm_compute in Hx.
    repeat (destruct Hx as [<-|Hx]; [lia|]). destruct Hx.
  - constructor; [exact H | constructor; [exact I | constructor]].
Qed.

Lemma fmt_a_pbyte : forall r, Forall pbyte r -> Forall pbyte (fmt F_addr [AS r]).
Proof.
  intros r H. apply fmt_pbyte_n with (n := length F_addr); [lia| |].
  - apply Forall_forall. intros x Hx. unfold pbyte. vm_compute in Hx.
    repeat (destruct Hx as [<-|Hx]; [lia|]). destruct Hx.
  - constructor; [exact H | constructor].
Qed.

Lemma u32_le4 : forall v, 0 <= v < 2 ^ 32 -> u32_enc v (le4 (Z_to_bv 64 v)).
Proof. intros v H. split; [exact H | reflexivity]. Qed.

Lemma le4_eqm : forall x y : word, bv_unsigned x mod 2 ^ 32 = bv_unsigned y mod 2 ^ 32 -> le4 x = le4 y.
Proof.
  intros x y H. unfold le4. rewrite <- (Z_to_le_bytes_mod 4 (bv_unsigned x) 32) by lia.
  rewrite <- (Z_to_le_bytes_mod 4 (bv_unsigned y) 32) by lia. rewrite H. reflexivity.
Qed.

Lemma sx32_small : forall z, 0 <= z < 2 ^ 31 -> sx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold sx32. rewrite unsigned_lit by lia. f_equal. apply bv_swrap_small.
  change (bv_half_modulus 32) with (2 ^ 31). lia.
Qed.

Lemma signed_small : forall z, 0 <= z < 2 ^ 31 -> bv_signed (Z_to_bv 64 z) = z.
Proof.
  intros z Hz. unfold bv_signed. rewrite unsigned_lit by lia. apply bv_swrap_small.
  change (bv_half_modulus 64) with (2 ^ 63). lia.
Qed.

Lemma swrap32_small : forall z, 0 <= z < 2 ^ 31 -> bv_swrap 32 z = z.
Proof. intros z Hz. apply bv_swrap_small. change (bv_half_modulus 32) with (2 ^ 31). lia. Qed.

Lemma mod32_of_mod64 : forall z, (z mod 2 ^ 64) mod 2 ^ 32 = z mod 2 ^ 32.
Proof.
  intros z. pose proof (Z.div_mod z (2 ^ 64) ltac:(lia)) as D.
  replace (z mod 2 ^ 64) with (z + (- (2 ^ 32 * (z / 2 ^ 64))) * 2 ^ 32) by lia.
  apply Z.mod_add. lia.
Qed.

Lemma swrap32_mod : forall z, bv_swrap 32 z mod 2 ^ 32 = z mod 2 ^ 32.
Proof.
  intros z. unfold bv_swrap, bv_wrap.
  change (bv_modulus 32) with (2 ^ 32). change (bv_half_modulus 32) with (2 ^ 31).
  rewrite Zminus_mod_idemp_l. f_equal. lia.
Qed.

(** `lw`, `addi 1`, `sw` of a 32-bit counter below 2^32 - 1: the stored word is the counter + 1. *)
Lemma le4_incr : forall r, 0 <= r < 2 ^ 32 - 1 ->
  le4 (Z_to_bv 64 (bv_unsigned (sx32 (Z_to_bv 64 r)) + 1)) = le4 (Z_to_bv 64 (r + 1)).
Proof.
  intros r Hr. apply le4_eqm. rewrite !unsigned_lit_wrap, !mod32_of_mod64.
  rewrite <- (Zplus_mod_idemp_l (bv_unsigned (sx32 (Z_to_bv 64 r))) 1 (2 ^ 32)).
  rewrite <- (Zplus_mod_idemp_l r 1 (2 ^ 32)).
  f_equal. f_equal.
  unfold sx32. rewrite unsigned_lit_wrap, mod32_of_mod64, unsigned_lit by lia.
  apply swrap32_mod.
Qed.

(** The bytes [off, off + n) of a concatenation. *)
Lemma fld_app_l : forall (l1 l2 : list byte) off n, (off + n <= length l1)%nat -> fld off n (l1 ++ l2) = fld off n l1.
Proof.
  intros l1 l2 off n H. unfold fld. rewrite skipn_app, firstn_app, length_skipn.
  replace (n - (length l1 - off))%nat with 0%nat by lia. rewrite firstn_O, app_nil_r. reflexivity.
Qed.
Lemma fld_app_r : forall (l1 l2 : list byte) off n, (length l1 <= off)%nat ->
  fld off n (l1 ++ l2) = fld (off - length l1) n l2.
Proof. intros l1 l2 off n H. unfold fld. rewrite skipn_app, (skipn_all2 l1) by lia. reflexivity. Qed.
Lemma fld_full : forall (l : list byte) off n, off = 0%nat -> length l = n -> fld off n l = l.
Proof. intros l off n -> <-. unfold fld. rewrite skipn_O. apply firstn_all. Qed.

Ltac flen := rewrite ?length_app, ?length_le4, ?length_zb; cbn [length]; lia.
Ltac fsimp := repeat first [ rewrite fld_app_l by flen | rewrite fld_app_r by flen ].
Ltac fmatch H :=
  revert H; fsimp; intros H;
  try (match type of H with context [fld ?o1 ?n ?L] =>
         match goal with |- context [fld ?o2 n L] => replace o2 with o1 by flen end end);
  exact H.

Lemma cstr_enc_112 : forall txt rest, Forall pbyte txt -> (length txt < 112)%nat ->
  Z.of_nat (length rest) = 111 - Z.of_nat (length txt) ->
  cstr_enc 112 txt (zb txt ++ [ZERO] ++ rest).
Proof.
  intros txt rest Hb Hl Hr. unfold cstr_enc.
  split; [rewrite !length_app, length_zb; cbn [length]; lia|].
  split; [exact Hl|]. split; [apply pbyte_nulfree; exact Hb|].
  rewrite !zs_app, (zs_zb txt Hb). rewrite firstn_app.
  replace (S (length txt) - length txt)%nat with 1%nat by lia.
  rewrite firstn_all2 by lia. reflexivity.
Qed.

(** n_kept < 8: the record SegModel.m_refuse builds, encoded. *)
Lemma enc_new : forall mc pend Q1 R K1 SL K2 N Q3 txt rest,
  mconf_encp pend mc (Q1 ++ R ++ (K1 ++ SL ++ K2) ++ N ++ Q3) ->
  Z.of_nat (length Q1) = 8200 -> Z.of_nat (length R) = 4 ->
  Z.of_nat (length K1) = 112 * Z.of_nat (length (mc_kept mc)) ->
  Z.of_nat (length SL) = 112 ->
  Z.of_nat (length K2) = 816 - 112 * Z.of_nat (length (mc_kept mc)) ->
  Z.of_nat (length N) = 4 -> Z.of_nat (length Q3) = 100 ->
  (length (mc_kept mc) < 8)%nat -> 0 <= mc_refused mc -> mc_refused mc + 1 < 2 ^ 32 ->
  Forall pbyte txt -> (length txt < 112)%nat -> Z.of_nat (length rest) = 111 - Z.of_nat (length txt) ->
  mconf_enc (MConf (mc_seg mc) (mc_overflow mc) (mc_refused mc + 1) (mc_kept mc ++ [(txt, pend)])
                   (mc_gen mc) (mc_reading mc))
            (Q1 ++ le4 (Z_to_bv 64 (mc_refused mc + 1)) ++ (K1 ++ (zb txt ++ [ZERO] ++ rest) ++ K2) ++
             le4 (Z_to_bv 64 (Z.of_nat (length (mc_kept mc)) + 1)) ++ Q3).
Proof.
  intros mc pend Q1 R K1 SL K2 N Q3 txt rest HE LQ1 LR LK1 LSL LK2 LN LQ3 Hn8 Hr0 Hrf Hb Ht Lrest.
  destruct HE as (HLb & Hseg32 & Hsegs & Hn & Hov & Hrefd & HKL & Hkept & Hknock & Hnk & Hgen & Hrd).
  assert (LSL' : Z.of_nat (length (zb txt ++ [ZERO] ++ rest)) = 112)
    by (rewrite !length_app, length_zb; cbn [length]; lia).
  unfold mconf_enc, mconf_encp, fldz in *.
  cbn [mc_seg mc_overflow mc_refused mc_kept mc_gen mc_reading] in *.
  unfold MC_N, MC_OVERFLOW, MC_REFUSED, MC_KEPT, MC_KNOCK, MC_NKEPT, MC_GEN, MC_READING, SEG_M_SIZE in *.
  split; [rewrite !length_app, !length_le4, length_zb; cbn [length]; lia|].
  split; [exact Hseg32|].
  split; [intros i Hi; specialize (Hsegs i Hi); fmatch Hsegs|].
  split; [fmatch Hn|].
  split; [fmatch Hov|].
  split; [fsimp; rewrite fld_full by flen; apply u32_le4; lia|].
  split; [rewrite length_app; cbn [length]; lia|].
  split.
  { intros i Hi. rewrite length_app in Hi; cbn [length] in Hi.
    destruct (Nat.lt_ge_cases i (length (mc_kept mc))) as [Hlt|Hge].
    - rewrite app_nth1 by exact Hlt. destruct (Hkept i Hlt) as [Hcs Hfl].
      split; [fmatch Hcs | fmatch Hfl].
    - assert (Ei : i = length (mc_kept mc)) by lia. subst i.
      rewrite app_nth2 by lia. rewrite Nat.sub_diag. cbn [nth fst snd].
      split.
      + fsimp. rewrite fld_full by flen. apply cstr_enc_112; assumption.
      + specialize (Hknock (length (mc_kept mc)) ltac:(lia)).
        rewrite Nat.eqb_refl, andb_true_r in Hknock. fmatch Hknock. }
  split.
  { intros i Hi. rewrite length_app in Hi; cbn [length] in Hi.
    assert (Hi' : (length (mc_kept mc) <= i < 8)%nat) by lia.
    specialize (Hknock i Hi').
    assert (Eb : (pend && (i =? length (mc_kept mc))%nat)%bool = false).
    { destruct (Nat.eqb_spec i (length (mc_kept mc))) as [E|E]; [lia | rewrite andb_false_r; reflexivity]. }
    rewrite Eb in Hknock. cbn [andb]. fmatch Hknock. }
  split.
  { fsimp. rewrite fld_full by flen. rewrite length_app; cbn [length].
    replace (Z.of_nat (length (mc_kept mc) + 1)) with (Z.of_nat (length (mc_kept mc)) + 1) by lia.
    apply u32_le4. lia. }
  split; [fmatch Hgen|].
  fmatch Hrd.
Qed.

(** n_kept = 8: only refused++. *)
Lemma enc_full : forall mc pend Q1 R MID N Q3,
  mconf_encp pend mc (Q1 ++ R ++ MID ++ N ++ Q3) ->
  Z.of_nat (length Q1) = 8200 -> Z.of_nat (length R) = 4 -> Z.of_nat (length MID) = 928 ->
  Z.of_nat (length N) = 4 -> Z.of_nat (length Q3) = 100 ->
  (length (mc_kept mc) = 8)%nat -> 0 <= mc_refused mc -> mc_refused mc + 1 < 2 ^ 32 ->
  mconf_enc (MConf (mc_seg mc) (mc_overflow mc) (mc_refused mc + 1) (mc_kept mc) (mc_gen mc) (mc_reading mc))
            (Q1 ++ le4 (Z_to_bv 64 (mc_refused mc + 1)) ++ MID ++ N ++ Q3).
Proof.
  intros mc pend Q1 R MID N Q3 HE LQ1 LR LMID LN LQ3 H8 Hr0 Hrf.
  destruct HE as (HLb & Hseg32 & Hsegs & Hn & Hov & Hrefd & HKL & Hkept & Hknock & Hnk & Hgen & Hrd).
  unfold mconf_enc, mconf_encp, fldz in *.
  cbn [mc_seg mc_overflow mc_refused mc_kept mc_gen mc_reading] in *.
  unfold MC_N, MC_OVERFLOW, MC_REFUSED, MC_KEPT, MC_KNOCK, MC_NKEPT, MC_GEN, MC_READING, SEG_M_SIZE in *.
  split; [rewrite !length_app, !length_le4; cbn [length]; lia|].
  split; [exact Hseg32|].
  split; [intros i Hi; specialize (Hsegs i Hi); fmatch Hsegs|].
  split; [fmatch Hn|].
  split; [fmatch Hov|].
  split; [fsimp; rewrite fld_full by flen; apply u32_le4; lia|].
  split; [exact HKL|].
  split.
  { intros i Hi. destruct (Hkept i Hi) as [Hcs Hfl]. split; [fmatch Hcs | fmatch Hfl]. }
  split; [intros i Hi; lia|].
  split; [fmatch Hnk|].
  split; [fmatch Hgen|].
  fmatch Hrd.
Qed.

(** * Memory helpers *)

Lemma zsplit : forall (mm : word -> option byte) (a n : Z) (l : list byte),
  bytes_at rsegs mm a l -> 0 <= n <= Z.of_nat (length l) ->
  exists l1 l2, l = l1 ++ l2 /\ Z.of_nat (length l1) = n /\
    bytes_at rsegs mm a l1 /\ bytes_at rsegs mm (a + n) l2.
Proof.
  intros mm a n l HB Hn.
  exists (firstn (Z.to_nat n) l), (skipn (Z.to_nat n) l).
  split; [symmetry; apply firstn_skipn|].
  assert (L1 : Z.of_nat (length (firstn (Z.to_nat n) l)) = n) by (rewrite length_firstn; lia).
  split; [exact L1|].
  rewrite <- (firstn_skipn (Z.to_nat n) l) in HB. apply bytes_at_app in HB as [B1 B2].
  rewrite L1 in B2. split; [exact B1 | exact B2].
Qed.

Lemma bytes_app2 : forall mm a (l1 l2 : list byte) (n1 : Z),
  bytes_at rsegs mm a l1 -> bytes_at rsegs mm (a + n1) l2 -> Z.of_nat (length l1) = n1 ->
  bytes_at rsegs mm a (l1 ++ l2).
Proof.
  intros mm a l1 l2 n1 B1 B2 L1. apply bytes_at_app. split; [exact B1|].
  replace (a + Z.of_nat (length l1)) with (a + n1) by lia. exact B2.
Qed.

Lemma wr_at_sub : forall mm a n k j, wr_at rsegs mm a n -> 0 <= k -> 0 <= j -> k + j <= n ->
  wr_at rsegs mm (a + k) j.
Proof.
  intros mm a n k j (Ha & Hn & H) Hk Hj Hkj. split; [lia|]. split; [lia|].
  intros i Hi. replace (a + k + i) with (a + (k + i)) by lia. apply H. lia.
Qed.

Lemma mk_cells : forall mm A (vR vN : word) (MID : list byte),
  bytes_at rsegs mm A (le4 vR) -> bytes_at rsegs mm (A + 4) MID -> bytes_at rsegs mm (A + 932) (le4 vN) ->
  Z.of_nat (length MID) = 928 -> wr_at rsegs mm A 936 ->
  rw_cells rsegs mm A [C4 vR; CB 928 MID; C4 vN].
Proof.
  intros mm A vR vN MID B1 B2 B3 LM HW.
  split.
  - split; [cbn [cells_wf cell_wf]; repeat split; first [exact I | lia]|].
    cbn [cells_bytes cbytes]. rewrite app_nil_r.
    apply (bytes_app2 mm A (le4 vR) (MID ++ le4 vN) 4); [exact B1 | | rewrite length_le4; lia].
    apply (bytes_app2 mm (A + 4) MID (le4 vN) 928); [exact B2 | | exact LM].
    replace (A + 4 + 928) with (A + 932) by lia. exact B3.
  - cbn [cells_size csize Nat.add].
    replace (Z.of_nat 936) with 936 by (vm_compute; reflexivity). exact HW.
Qed.

Lemma mk_cb : forall mm A (l : list byte) (n : Z),
  bytes_at rsegs mm A l -> Z.of_nat (length l) = n -> wr_at rsegs mm A n ->
  rw_cells rsegs mm A [CB (Z.to_nat n) l].
Proof.
  intros mm A l n HB Hl HW. split.
  - split; [cbn [cells_wf cell_wf]; split; [lia | exact I]|].
    cbn [cells_bytes cbytes]. rewrite app_nil_r. exact HB.
  - cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r, Z2Nat.id by lia. exact HW.
Qed.

Lemma outside_dec : forall W x, outside W x \/ ~ outside W x.
Proof.
  induction W as [|[lo1 hi1] W IH]; intros x; cbn [outside]; [left; exact I|].
  destruct (IH x) as [H|H]; [|right; intros [_ H']; exact (H H')].
  destruct (Z_le_dec lo1 x); destruct (Z_lt_dec x hi1);
    [right; intros [H' _]; lia | left; split; [lia | exact H] ..].
Qed.

Lemma task_mem_munch : forall segs W mm mm', MemNorm.task_mem segs mm -> munch W mm mm' ->
  (forall x : word, ~ outside W (bv_unsigned x) -> mrd segs mm x <> None) -> MemNorm.task_mem segs mm'.
Proof.
  intros segs W mm mm' T MU P x b Hx.
  destruct (outside_dec W (bv_unsigned x)) as [Ho|Ho].
  - rewrite (MU x Ho) in Hx. exact (T x b Hx).
  - specialize (P x Ho). unfold mrd in P. destruct (mm x) as [b0|] eqn:E.
    + exact (T x b0 E).
    + left. intros Hf. apply P. exact (MemNorm.seg_rom_unmapped segs x Hf).
Qed.

Lemma ro_str : forall mm a l, mem_inv rsegs mm -> 0 <= a -> a + Z.of_nat (length l) <= 2 ^ 64 ->
  ro_bytes_b rsegs a l = true -> bytes_at rsegs mm a l.
Proof. intros mm a l MI H0 H1 H. apply ro_bytes_at; auto. apply ro_bytes_b_sound. exact H. Qed.

(** The two format literals in .rodata. *)
Lemma fmt_al_bytes : forall mm, mem_inv rsegs mm -> bytes_at rsegs mm MR_FMT_AL (zb (F_addr_line ++ [0])).
Proof.
  intros mm MI. rewrite zb_app.
  apply ro_str; [exact MI | unfold MR_FMT_AL; lia | | vm_compute; reflexivity].
  rewrite length_app, !length_zb. cbn [length].
  change (length F_addr_line) with 7%nat. unfold MR_FMT_AL. lia.
Qed.

Lemma fmt_a_bytes : forall mm, mem_inv rsegs mm -> bytes_at rsegs mm MR_FMT_A (zb (F_addr ++ [0])).
Proof.
  intros mm MI. rewrite zb_app.
  apply ro_str; [exact MI | unfold MR_FMT_A; lia | | vm_compute; reflexivity].
  rewrite length_app, !length_zb. cbn [length].
  change (length F_addr) with 4%nat. unfold MR_FMT_A. lia.
Qed.

(** struct mconf is 9236 bytes and the block is 16-aligned, so 4 bytes past its end are present (blk_slack), which
    is what c->reading's word-at-a-time reader may take. *)
Lemma slack_mod : forall a, a mod 16 = 0 -> (- (a + 9236)) mod 8 = 4.
Proof.
  intros a Ha.
  assert (Ec : a = 8 * (a / 8)).
  { assert (H8 : a mod 8 = 0) by (Z.div_mod_to_equations; lia). Z.div_mod_to_equations; lia. }
  replace (- (a + 9236)) with ((- 9236) + (- (a / 8)) * 8) by lia.
  rewrite Z.mod_add by lia. vm_compute. reflexivity.
Qed.

Lemma slack_ok : forall a L, a mod 16 = 0 -> 0 <= L <= 95 -> (- (a + 9140 + L + 1)) mod 8 <= 99 - L.
Proof.
  intros a L Ha HL.
  assert (Ec : a = 8 * (a / 8)).
  { assert (H8 : a mod 8 = 0) by (Z.div_mod_to_equations; lia). Z.div_mod_to_equations; lia. }
  replace (- (a + 9140 + L + 1)) with ((- 9141 - L) + (- (a / 8)) * 8) by lia.
  rewrite Z.mod_add by lia.
  destruct (Z.le_gt_cases L 92) as [Hle|Hgt].
  - pose proof (Z.mod_pos_bound (- 9141 - L) 8 ltac:(lia)). lia.
  - assert (EL : L = 93 \/ L = 94 \/ L = 95) by lia.
    destruct EL as [E1 | [E1 | E1]]; subst L; vm_compute; discriminate.
Qed.

Ltac dj := cbn [disjoint_from]; simpl_sizes; rewrite ?length_zb; cbn [length];
           repeat split; first [exact I | lia].

(** * [mr_snprintf] from the callee's contract *)

Lemma pargs_addr : forall r,
  SegPrintfBridge.sp_pargs F_addr [AS r] = [Printf_model.PA_s (cut_nul r)].
Proof. intros r. vm_compute. reflexivity. Qed.

Lemma mr_snprintf_of_m : snprintf_m_contract -> mr_snprintf.
Proof.
  intros HM.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         F fc m lo junk rd line f args Hshape HFB HSTR HRDL HCELL HN1 HD0 HDA HNOIMG HSTK HKK HENV MI.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp; change (bv_modulus 64) with (2 ^ 64) in Rsp.
  pose proof (bv_unsigned_in_range 64 a2) as Ra2; change (bv_modulus 64) with (2 ^ 64) in Ra2.
  destruct HSTR as (HRDB & slack & HSB & HSLm & HR0 & HRA1 & HRA2).
  assert (Hcut : cut_nul rd = rd) by (apply cut_nul_id, pbyte_nulfree; exact HRDB).
  destruct HENV as (FRM0 & TM0 & (SG1 & g & SG2) & HLOI & HSP63).
  unfold SA, SEG_UBSAN in HLOI, SG1, SG2; cbn [sa_img_end sa_got_guard sa_guard] in HLOI, SG1, SG2.
  (* the model's text and the argument of the %s conversion *)
  assert (HARG : pf_arg_ok m (bv_unsigned sp) lo (bv_unsigned a0) (bv_unsigned a1) a3 (APtr (cut_nul rd))).
  { rewrite Hcut. cbn [pf_arg_ok]. split.
    - revert HRDB. apply Forall_impl. intros x Hx. unfold pbyte in Hx. lia.
    - exists slack. split; [exact HSB|]. split; [exact HSLm|]. split; [exact HR0|].
      split; [exact HRA1 | exact HRA2]. }
  destruct Hshape as [(-> & -> & Ha2 & Ha4 & Hline) | (-> & -> & Ha2)].
  - (* "%s:%d: " *)
    assert (HINT : Prelim.zlength (fmt F_addr_line [AS rd; AI line]) < FmtFp.INT_MAX).
    { unfold Prelim.zlength, FmtFp.INT_MAX.
      pose proof (fmt_len F_addr_line [AS rd; AI line]) as HFL.
      change (length F_addr_line) with 7%nat in HFL.
      cbn [arglens arglen] in HFL. lia. }
    eapply evt_mono.
    + eapply (HM ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                 t3 t4 t5 t6 F fc m lo g F_addr_line
                 (SegPrintfBridge.sp_pargs F_addr_line [AS rd; AI line])
                 (snprintf_r F_addr_line [AS rd; AI line]) (fmt F_addr_line [AS rd; AI line]) junk []).
      * rewrite pf_bytes_zb. exact HFB.
      * rewrite Ha2. unfold MR_FMT_AL, RO_LO. lia.
      * rewrite Ha2. unfold MR_FMT_AL, RO_END. change (length F_addr_line) with 7%nat. lia.
      * apply Forall_forall. intros x Hx. vm_compute in Hx.
        repeat (destruct Hx as [<-|Hx]; [lia|]). destruct Hx.
      * vm_compute. reflexivity.
      * rewrite SegPrintfBridge.pargs_addr_line. cbn [pm_args_ok pm_arg_ok app].
        split; [exact HARG|]. split; [|exact I].
        cbn [pf_arg_ok]. split; [lia|]. rewrite Ha4. reflexivity.
      * cbn [u64s]. apply bytes_at_nil. lia.
      * cbn [length]. change (Z.of_nat 0) with 0. lia.
      * cbn [length]. change (Z.of_nat 0) with 0. unfold PRINTF_K in HKK. lia.
      * exact (SegPrintfBridge.pm_addr_line rd line ltac:(lia) HINT).
      * exact HCELL.
      * exact HN1.
      * exact HD0.
      * exact HDA.
      * exact HNOIMG.
      * exact HSTK.
      * unfold SNPRINTF_K. unfold PRINTF_K in HKK. lia.
      * unfold IMG_END. lia.
      * exact HSP63.
      * exact FRM0.
      * exact MI.
      * exact TM0.
      * unfold GOT_GUARD, GUARD. exact SG1.
      * unfold GUARD. exact SG2.
    + intros ms' PO. unfold printf_post in PO.
      destruct PO as (y0 & y1 & y2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & Ft & fc' & m' &
                      -> & MU & WM & MI' & TM' & FRM' & FEQ' & ST' & BD).
      unfold mr_post, ret_post_fp.
      exists y0, y1, y2, b1, b2, b3, b4, b5, b6, b7, u3, u4, u5, u6, Ft, fc', m'.
      split; [reflexivity|]. split; [exact FRM'|]. split; [exact FEQ'|]. split; [exact MU|].
      split; [exact WM|]. split; [exact MI'|]. split; [exact TM'|]. split; [exact ST'|].
      rewrite pf_bytes_zb, zb_app in BD. exact BD.
  - (* "%s: " *)
    assert (HINT : Prelim.zlength (fmt F_addr [AS rd]) < FmtFp.INT_MAX).
    { unfold Prelim.zlength, FmtFp.INT_MAX.
      pose proof (fmt_len F_addr [AS rd]) as HFL.
      change (length F_addr) with 4%nat in HFL.
      cbn [arglens arglen] in HFL. lia. }
    eapply evt_mono.
    + eapply (HM ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                 t3 t4 t5 t6 F fc m lo g F_addr
                 (SegPrintfBridge.sp_pargs F_addr [AS rd])
                 (snprintf_r F_addr [AS rd]) (fmt F_addr [AS rd]) junk []).
      * rewrite pf_bytes_zb. exact HFB.
      * rewrite Ha2. unfold MR_FMT_A, RO_LO. lia.
      * rewrite Ha2. unfold MR_FMT_A, RO_END. change (length F_addr) with 4%nat. lia.
      * apply Forall_forall. intros x Hx. vm_compute in Hx.
        repeat (destruct Hx as [<-|Hx]; [lia|]). destruct Hx.
      * vm_compute. reflexivity.
      * rewrite pargs_addr. cbn [pm_args_ok pm_arg_ok app]. split; [exact HARG | exact I].
      * cbn [u64s]. apply bytes_at_nil. lia.
      * cbn [length]. change (Z.of_nat 0) with 0. lia.
      * cbn [length]. change (Z.of_nat 0) with 0. unfold PRINTF_K in HKK. lia.
      * exact (SegPrintfBridge.pm_addr rd HINT).
      * exact HCELL.
      * exact HN1.
      * exact HD0.
      * exact HDA.
      * exact HNOIMG.
      * exact HSTK.
      * unfold SNPRINTF_K. unfold PRINTF_K in HKK. lia.
      * unfold IMG_END. lia.
      * exact HSP63.
      * exact FRM0.
      * exact MI.
      * exact TM0.
      * unfold GOT_GUARD, GUARD. exact SG1.
      * unfold GUARD. exact SG2.
    + intros ms' PO. unfold printf_post in PO.
      destruct PO as (y0 & y1 & y2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & Ft & fc' & m' &
                      -> & MU & WM & MI' & TM' & FRM' & FEQ' & ST' & BD).
      unfold mr_post, ret_post_fp.
      exists y0, y1, y2, b1, b2, b3, b4, b5, b6, b7, u3, u4, u5, u6, Ft, fc', m'.
      split; [reflexivity|]. split; [exact FRM'|]. split; [exact FEQ'|]. split; [exact MU|].
      split; [exact WM|]. split; [exact MI'|]. split; [exact TM'|]. split; [exact ST'|].
      rewrite pf_bytes_zb, zb_app in BD. exact BD.
Qed.

(** * The walk *)

Section W.
Variables (ra sp gp tp s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo c ln : Z) (mc : mconf) (knock : bool)
  (bs : list byte).
Hypothesis HSN : mr_snprintf.
Hypothesis Hc0 : c <> 0.
Hypothesis Hc16 : c mod 16 = 0.
Hypothesis Himg : blk_noimg rsegs c SEG_M_SIZE.
Hypothesis HB0 : bytes_at rsegs m c bs.
Hypothesis HE0 : mconf_encp knock mc bs.
Hypothesis HW0 : wr_at rsegs m c SEG_M_SIZE.
Hypothesis HSLK : blk_slack rsegs m c SEG_M_SIZE.
Hypothesis Hap : apart c (SEG_M_SIZE + 4) lo (bv_unsigned sp).
Hypothesis Hln : 0 <= ln <= 65536.
Hypothesis Hrf : mc_refused mc + 1 < 2 ^ 32.
Hypothesis HENV : printf_env m fc lo (bv_unsigned sp).
Hypothesis HST : stack_ok rsegs m lo (bv_unsigned sp) M_REFUSE_STACK.
Hypothesis MI0 : mem_inv rsegs m.

Local Abbreviation Post :=
  (ret_void_fp ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m
     (m_refuse_W (bv_unsigned sp) c mc) lo
     (fun m' => mconf_at rsegs m' c (m_refuse mc ln knock))).

Ltac nums :=
  pose proof (bv_unsigned_in_range 64 sp) as Rsp; change (bv_modulus 64) with (2 ^ 64) in Rsp;
  pose proof HST as (ST0 & HKD & HSP16 & HNR); unfold M_REFUSE_STACK, PRINTF_K in HKD;
  pose proof HENV as (FRM0 & TM0 & SSP0 & HLOI & HSP63);
  pose proof Hap as HAP; unfold apart, SEG_M_SIZE in HAP;
  pose proof (bytes_at_bound _ _ _ _ HB0) as BB0;
  pose proof HE0 as (HLb & Hseg32 & Hsegs & Hn & Hov & Hrefd & HKL & Hkept & Hknock & Hnk & Hgen & Hrd);
  unfold SEG_M_SIZE in HLb;
  pose proof (proj1 Hrefd) as Hr32;
  pose proof (proj1 (proj2 Hrd)) as Hrdlen;
  assert (LO0 : 0 <= lo) by (destruct ST0 as [H0 _]; exact H0).

(** Every byte m_refuse may write was present at entry (what task_mem needs). *)
Lemma pres : forall x : word, ~ outside (m_refuse_W (bv_unsigned sp) c mc) (bv_unsigned x) ->
  mrd rsegs m x <> None.
Proof.
  intros x Hx. nums.
  assert (HIN : bv_unsigned sp - 5952 <= bv_unsigned x < bv_unsigned sp \/ c <= bv_unsigned x < c + 9236).
  { unfold m_refuse_W, M_REFUSE_STACK, PRINTF_K, kept_addr, MC_KEPT, MC_KEPT_LEN, MC_NKEPT, MC_REFUSED in Hx.
    destruct (Z.of_nat (length (mc_kept mc)) <? 8) eqn:E8; cbn [app outside] in Hx;
      [apply Z.ltb_lt in E8 | apply Z.ltb_ge in E8]; lia. }
  assert (E : wa (bv_unsigned x) = x) by (unfold wa; apply Z_to_bv_bv_unsigned).
  destruct HIN as [Hs|Hb].
  - destruct ST0 as (_ & _ & STa). destruct (STa (bv_unsigned x) ltac:(lia)) as [_ (b & Hb')].
    rewrite E in Hb'. rewrite Hb'. discriminate.
  - destruct HB0 as (_ & _ & Bb). rewrite <- E.
    replace (bv_unsigned x) with (c + Z.of_nat (Z.to_nat (bv_unsigned x - c))) by lia.
    rewrite Bb by lia. intros C. apply nth_error_None in C. lia.
Qed.

Lemma pres_stk : forall x : word, ~ outside [(bv_unsigned sp - 5952, bv_unsigned sp)] (bv_unsigned x) ->
  mrd rsegs m x <> None.
Proof.
  intros x Hx. nums. cbn [outside] in Hx.
  destruct ST0 as (_ & _ & STa). destruct (STa (bv_unsigned x) ltac:(lia)) as [_ (b & Hb')].
  assert (E : wa (bv_unsigned x) = x) by (unfold wa; apply Z_to_bv_bv_unsigned).
  rewrite E in Hb'. rewrite Hb'. discriminate.
Qed.

(** The slot kept[n_kept] is free of the image's reserved segments, because the whole block is. *)
Lemma slot_noimg : forall k n, 0 <= k -> 0 <= n -> k + n <= 9236 -> blk_noimg rsegs (c + k) n.
Proof.
  intros k n Hk Hn Hkn i Hi s Hs.
  replace (c + k + i) with (c + (k + i)) by lia.
  apply (Himg (k + i)); [unfold SEG_M_SIZE; lia | exact Hs].
Qed.

(** printf's machine after the prologue's two stores, on the window [sp - 5952, sp - 16) the call gets. *)
Lemma env_after : forall mm, munch [(bv_unsigned sp - 5952, bv_unsigned sp)] m mm ->
  printf_env mm fc (bv_unsigned sp - 5952) (bv_unsigned sp + -16).
Proof.
  intros mm MU. nums.
  destruct SSP0 as (SG1 & g & SG2).
  assert (HG : sa_got_guard SA + 8 <= lo /\ sa_guard SA + 8 <= lo /\ 0 <= sa_got_guard SA
               /\ 0 <= sa_guard SA).
  { unfold SA, SEG_UBSAN in HLOI |- *; cbn [sa_got_guard sa_guard sa_img_end] in HLOI |- *; lia. }
  split; [exact FRM0|].
  split; [exact (task_mem_munch rsegs _ m mm TM0 MU pres_stk)|].
  split.
  { split.
    - eapply bytes_at_transport; [exact SG1 | exact MU |]. rewrite length_le8. dj.
    - exists g. eapply bytes_at_transport; [exact SG2 | exact MU |]. rewrite length_le8. dj. }
  split; [lia | lia].
Qed.

(** The bytes of c->reading are nonzero bytes. *)
Lemma reading_pbyte : forall RD, cstr_enc 96 (mc_reading mc) RD -> Forall pbyte (mc_reading mc).
Proof.
  intros RD (Hl96 & Hlt & Hnf & Hpre).
  apply Forall_forall. intros x Hx. unfold pbyte.
  assert (Hin : In x (zs RD)).
  { rewrite <- (firstn_skipn (S (length (mc_reading mc))) (zs RD)). apply in_or_app. left.
    rewrite Hpre. apply in_or_app. left. exact Hx. }
  assert (Hne : x <> 0) by (intros ->; exact (Hnf Hx)).
  unfold zs in Hin. apply in_map_iff in Hin as (b & <- & _).
  pose proof (bv_unsigned_in_range 8 b) as Hb. change (bv_modulus 8) with 256%Z in Hb. lia.
Qed.

(** c->reading as snprintf's %s argument: the 96-byte field, then the block's 4 slack bytes. *)
Lemma reading_str : forall (mm : word -> option byte) (D : Z) (RD sl : list byte),
  bytes_at rsegs mm (c + 9140) RD -> cstr_enc 96 (mc_reading mc) RD ->
  bytes_at rsegs mm (c + 9236) sl -> 4 <= Z.of_nat (length sl) ->
  c + 8204 <= D -> D + 112 <= c + 9100 ->
  mr_str mm (bv_unsigned sp + -16) (bv_unsigned sp - 5952) D 112 (c + 9140) (mc_reading mc).
Proof.
  intros mm D RD sl BRD HE BSL HSL4 HD1 HD2. nums.
  pose proof (reading_pbyte RD HE) as HB.
  destruct HE as (Hl96 & Hlt & Hnf & Hpre).
  split; [exact HB|].
  (* RD = zb (reading ++ [0]) ++ tail *)
  assert (Ek : firstn (S (length (mc_reading mc))) RD = zb (mc_reading mc ++ [0])).
  { rewrite <- Hpre. unfold zb, zs. rewrite firstn_map, map_map.
    rewrite (map_ext (fun x : byte => Z_to_bv 8 (bv_unsigned x)) id)
      by (intros b; apply bv_eq; rewrite Z_to_bv_unsigned; apply bv_wrap_small; apply bv_unsigned_in_range).
    rewrite map_id. reflexivity. }
  pose proof (firstn_skipn (S (length (mc_reading mc))) RD) as Esp.
  rewrite Ek in Esp.
  destruct (zsplit mm (c + 9236) 4 sl BSL ltac:(lia)) as (SL4 & SLr & Esl & LSL4 & BSL4 & _).
  exists (skipn (S (length (mc_reading mc))) RD ++ SL4).
  assert (Llen : Z.of_nat (length (zb (mc_reading mc ++ [0]))) = Z.of_nat (length (mc_reading mc)) + 1)
    by (rewrite length_zb, length_app; cbn [length]; lia).
  assert (Lsk : Z.of_nat (length (skipn (S (length (mc_reading mc))) RD)) = 95 - Z.of_nat (length (mc_reading mc)))
    by (rewrite length_skipn; lia).
  split.
  { rewrite app_assoc, Esp.
    apply (bytes_app2 mm (c + 9140) RD SL4 96); [exact BRD | | lia].
    replace (c + 9140 + 96) with (c + 9236) by lia. exact BSL4. }
  rewrite length_app, Nat2Z.inj_add, Lsk, LSL4.
  split.
  { eapply Z.le_trans; [apply slack_ok; [exact Hc16 | lia] | lia]. }
  split; [lia|].
  split; lia.
Qed.

(** The exit at 0x15008 when n_kept = 8: only refused++, then the epilogue. *)
Lemma tail_full : forall (mk : word -> option byte) (Fk : bvmap 5 word) (fck : bv 32)
    (x1 y5 y6 y7 z0 z1 z2 z3 z4 z5 z6 z7 u3 u4 u5 u6 : word)
    (Q1 MID Q3 : list byte) (vN : word),
  (length (mc_kept mc) = 8)%nat ->
  rw_cells rsegs mk (bv_unsigned sp + -16) [C8 s0; C8 ra] ->
  rw_cells rsegs mk (c + 8200) [C4 (Z_to_bv 64 (mc_refused mc)); CB 928 MID; C4 vN] ->
  bytes_at rsegs mk c Q1 -> Z.of_nat (length Q1) = 8200 ->
  bytes_at rsegs mk (c + 9136) Q3 -> Z.of_nat (length Q3) = 100 ->
  Z.of_nat (length MID) = 928 ->
  mconf_encp knock mc (Q1 ++ le4 (Z_to_bv 64 (mc_refused mc)) ++ MID ++ le4 vN ++ Q3) ->
  stk rsegs mk lo (bv_unsigned sp + -16) -> mem_inv rsegs mk ->
  munch [(bv_unsigned sp - 5952, bv_unsigned sp); (c + 8200, c + 8204)] m mk ->
  wmono rsegs m mk -> frm0 fck -> (forall k : reg, bv_unsigned k <> 10 -> reg_get Fk k = reg_get F k) ->
  evt rsegs Post
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp y5 y6 y7 (Z_to_bv 64 (c + 8200)) s1
             z0 z1 z2 z3 z4 z5 z6 z7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
        Fk (Z_to_bv 64 0x15008) fck None mk (seg_rom rsegs)).
Proof.
  intros mk Fk fck x1 y5 y6 y7 z0 z1 z2 z3 z4 z5 z6 z7 u3 u4 u5 u6 Q1 MID Q3 vN
         H8 FR CS BQ1 LQ1 BQ3 LQ3 LMID ENC0 ST MI MU WM FRM FEQ.
  nums. pose proof TM0 as TM00. pose proof pres as PRES.
  assert (SUB : sub_fp [(bv_unsigned sp - 5952, bv_unsigned sp); (c + 8200, c + 8204)]
                       (m_refuse_W (bv_unsigned sp) c mc)).
  { unfold sub_fp, m_refuse_W, M_REFUSE_STACK, PRINTF_K, MC_REFUSED, MC_NKEPT, kept_addr, MC_KEPT, MC_KEPT_LEN.
    replace (Z.of_nat (length (mc_kept mc)) <? 8) with false by (symmetry; apply Z.ltb_ge; lia).
    cbn [app outside]. intros x Hx. split; [lia|]. split; [lia | exact I]. }
  zstep. zstep. zstep.
  zstep. zstep. zstep. zstep.
  release_frame FR ST (bv_unsigned sp).
  apply evt_done. hnf.
  do 18 eexists.
  split; [reflexivity|].
  split; [exact FRM|].
  split; [exact FEQ|].
  split; [eapply munch_weaken; [exact SUB | exact MU]|].
  split; [exact WM|].
  split; [exact MI|].
  split; [eapply task_mem_munch; [exact TM00 | eapply munch_weaken; [exact SUB | exact MU] | exact PRES]|].
  split; [exact ST|].
  destruct CS as [[_ HBc] _]. cbn [cells_bytes cbytes] in HBc. rewrite app_nil_r in HBc.
  rewrite (le4_incr (mc_refused mc)) in HBc by lia.
  exists (Q1 ++ le4 (Z_to_bv 64 (mc_refused mc + 1)) ++ MID ++ le4 vN ++ Q3).
  split.
  { apply bytes_at_app in HBc as [HB1 HB2]. rewrite length_le4 in HB2.
    change (Z.of_nat 4) with 4 in HB2.
    apply bytes_at_app in HB2 as [HB3 HB4]. rewrite LMID in HB4.
    apply (bytes_app2 _ c Q1 _ 8200); [exact BQ1 | | exact LQ1].
    apply (bytes_app2 _ (c + 8200) _ _ 4); [exact HB1 | | rewrite length_le4; lia].
    apply (bytes_app2 _ (c + 8200 + 4) _ _ 928); [exact HB3 | | exact LMID].
    apply (bytes_app2 _ (c + 8200 + 4 + 928) _ _ 4); [exact HB4 | | rewrite length_le4; lia].
    replace (c + 8200 + 4 + 928 + 4) with (c + 9136) by lia. exact BQ3. }
  unfold m_refuse. cbv zeta.
  replace (Z.of_nat (length (mc_kept mc)) <? 8) with false by (symmetry; apply Z.ltb_ge; lia).
  eapply enc_full; try eassumption; rewrite ?length_le4; lia.
Qed.

(** The join at 0x14ff8 when n_kept < 8: n_kept++ (with UBSan's overflow check), refused++, the epilogue. *)
Lemma tail_kept : forall (mk : word -> option byte) (Fk : bvmap 5 word) (fck : bv 32)
    (x1 y5 y6 y7 z0 z1 z2 z3 z4 z5 z6 z7 u3 u4 u5 u6 : word)
    (Q1 K1 SL K2 Q3 SLb : list byte) (txt : list Z),
  (length (mc_kept mc) < 8)%nat ->
  m_refuse mc ln knock = MConf (mc_seg mc) (mc_overflow mc) (mc_refused mc + 1)
                               (mc_kept mc ++ [(txt, knock)]) (mc_gen mc) (mc_reading mc) ->
  Forall pbyte txt -> (length txt < 112)%nat ->
  rw_cells rsegs mk (bv_unsigned sp + -16) [C8 s0; C8 ra] ->
  rw_cells rsegs mk (c + 8200)
    [C4 (Z_to_bv 64 (mc_refused mc)); CB 928 (K1 ++ (zb txt ++ [ZERO] ++ SLb) ++ K2);
     C4 (Z_to_bv 64 (Z.of_nat (length (mc_kept mc))))] ->
  bytes_at rsegs mk c Q1 -> Z.of_nat (length Q1) = 8200 ->
  bytes_at rsegs mk (c + 9136) Q3 -> Z.of_nat (length Q3) = 100 ->
  Z.of_nat (length K1) = 112 * Z.of_nat (length (mc_kept mc)) ->
  Z.of_nat (length SL) = 112 ->
  Z.of_nat (length K2) = 816 - 112 * Z.of_nat (length (mc_kept mc)) ->
  Z.of_nat (length SLb) = 111 - Z.of_nat (length txt) ->
  mconf_encp knock mc
    (Q1 ++ le4 (Z_to_bv 64 (mc_refused mc)) ++ (K1 ++ SL ++ K2) ++
     le4 (Z_to_bv 64 (Z.of_nat (length (mc_kept mc)))) ++ Q3) ->
  stk rsegs mk lo (bv_unsigned sp + -16) -> mem_inv rsegs mk ->
  munch [(bv_unsigned sp - 5952, bv_unsigned sp);
         (c + 8204 + 112 * Z.of_nat (length (mc_kept mc)),
          c + 8204 + 112 * Z.of_nat (length (mc_kept mc)) + 112);
         (c + 9132, c + 9136); (c + 8200, c + 8204)] m mk ->
  wmono rsegs m mk -> frm0 fck -> (forall k : reg, bv_unsigned k <> 10 -> reg_get Fk k = reg_get F k) ->
  evt rsegs Post
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp y5 y6 y7 (Z_to_bv 64 (c + 8200)) s1
             z0 z1 z2 z3 z4 z5 z6 z7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
        Fk (Z_to_bv 64 0x14ff8) fck None mk (seg_rom rsegs)).
Proof.
  intros mk Fk fck x1 y5 y6 y7 z0 z1 z2 z3 z4 z5 z6 z7 u3 u4 u5 u6 Q1 K1 SL K2 Q3 SLb txt
         H8 HMOD HTB HTL FR CS BQ1 LQ1 BQ3 LQ3 LK1 LSL LK2 LSLb ENC0 ST MI MU WM FRM FEQ.
  nums. pose proof TM0 as TM00. pose proof pres as PRES.
  assert (SUB : sub_fp
    [(bv_unsigned sp - 5952, bv_unsigned sp);
     (c + 8204 + 112 * Z.of_nat (length (mc_kept mc)), c + 8204 + 112 * Z.of_nat (length (mc_kept mc)) + 112);
     (c + 9132, c + 9136); (c + 8200, c + 8204)] (m_refuse_W (bv_unsigned sp) c mc)).
  { unfold sub_fp, m_refuse_W, M_REFUSE_STACK, PRINTF_K, MC_REFUSED, MC_NKEPT, kept_addr, MC_KEPT, MC_KEPT_LEN.
    replace (Z.of_nat (length (mc_kept mc)) <? 8) with true by (symmetry; apply Z.ltb_lt; lia).
    cbn [app outside]. intros x Hx. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia | exact I]. }
  (* 0x14ff8 lw a1,0x3a4(s0); addiw a0,a1,1; blt a0,a1 -> trap; sw a0,0x3a4(s0) *)
  zstep. rewrite sx32_small by lia.
  zstep. rewrite swrap32_small by lia.
  zstep.
  if_cases KO; zify_cond KO.
  { exfalso. rewrite !signed_small in KO by lia. lia. }
  zstep.
  (* 0x15008 lw a0,0(s0); addi a0,a0,1; sw a0,0(s0) *)
  zstep. zstep. zstep.
  zstep. zstep. zstep. zstep.
  release_frame FR ST (bv_unsigned sp).
  apply evt_done. hnf.
  do 18 eexists.
  split; [reflexivity|].
  split; [exact FRM|].
  split; [exact FEQ|].
  split; [eapply munch_weaken; [exact SUB | exact MU]|].
  split; [exact WM|].
  split; [exact MI|].
  split; [eapply task_mem_munch; [exact TM00 | eapply munch_weaken; [exact SUB | exact MU] | exact PRES]|].
  split; [exact ST|].
  destruct CS as [[_ HBc] _]. cbn [cells_bytes cbytes] in HBc. rewrite app_nil_r in HBc.
  rewrite (le4_incr (mc_refused mc)) in HBc by lia.
  exists (Q1 ++ le4 (Z_to_bv 64 (mc_refused mc + 1)) ++ (K1 ++ (zb txt ++ [ZERO] ++ SLb) ++ K2) ++
          le4 (Z_to_bv 64 (Z.of_nat (length (mc_kept mc)) + 1)) ++ Q3).
  assert (LMID : Z.of_nat (length (K1 ++ (zb txt ++ [ZERO] ++ SLb) ++ K2)) = 928)
    by (rewrite !length_app, length_zb; cbn [length]; lia).
  split.
  { apply bytes_at_app in HBc as [HB1 HB2]. rewrite length_le4 in HB2.
    change (Z.of_nat 4) with 4 in HB2.
    apply (bytes_app2 _ c Q1 _ 8200); [exact BQ1 | | exact LQ1].
    apply (bytes_app2 _ (c + 8200) _ _ 4); [exact HB1 | | rewrite length_le4; lia].
    rewrite (app_assoc (K1 ++ (zb txt ++ [ZERO] ++ SLb) ++ K2)
                       (le4 (Z_to_bv 64 (Z.of_nat (length (mc_kept mc)) + 1))) Q3).
    apply (bytes_app2 _ (c + 8200 + 4) _ Q3 932);
      [ exact HB2
      | replace (c + 8200 + 4 + 932) with (c + 9136) by lia; exact BQ3
      | rewrite !length_app, !length_le4, !length_zb; cbn [length]; lia ]. }
  rewrite HMOD.
  eapply enc_new; try eassumption; rewrite ?length_le4; lia.
Qed.

(** The slot address the code computes. *)
Ltac fix_slot :=
  match goal with
  | |- context [Z_to_bv 64 (c + 8204 + ?E)] =>
      replace (c + 8204 + E) with (c + 8204 + 112 * Z.of_nat (length (mc_kept mc)))
        by (rewrite ?unsigned_lit by lia; rewrite !Z.shiftl_mul_pow2 by lia;
            rewrite !Z.mod_small by lia; lia)
  end.

(** After a call (at 0x14ff8): carry the block's pieces and the frame over the callee's footprint, rebuild the
    cells with the new text in the slot, join the two stack windows, and run the join. *)
Lemma after_call : forall (mm mk : word -> option byte) (Fk : bvmap 5 word) (fck : bv 32)
    (x1 y5 y6 y7 z0 z1 z2 z3 z4 z5 z6 z7 u3 u4 u5 u6 : word)
    (Q1 K1 SL K2 Q3 : list byte) (txt : list Z),
  Z.of_nat (length (mc_kept mc)) <= 7 ->
  m_refuse mc ln knock = MConf (mc_seg mc) (mc_overflow mc) (mc_refused mc + 1)
                               (mc_kept mc ++ [(txt, knock)]) (mc_gen mc) (mc_reading mc) ->
  Forall pbyte txt -> (length txt < 112)%nat ->
  mconf_encp knock mc
    (Q1 ++ le4 (Z_to_bv 64 (mc_refused mc)) ++ (K1 ++ SL ++ K2) ++
     le4 (Z_to_bv 64 (Z.of_nat (length (mc_kept mc)))) ++ Q3) ->
  Z.of_nat (length Q1) = 8200 -> Z.of_nat (length Q3) = 100 ->
  Z.of_nat (length K1) = 112 * Z.of_nat (length (mc_kept mc)) ->
  Z.of_nat (length SL) = 112 ->
  Z.of_nat (length K2) = 816 - 112 * Z.of_nat (length (mc_kept mc)) ->
  bytes_at rsegs mm c Q1 ->
  bytes_at rsegs mm (c + 8200) (le4 (Z_to_bv 64 (mc_refused mc))) ->
  bytes_at rsegs mm (c + 8204) K1 ->
  bytes_at rsegs mm (c + 8204 + 112 * Z.of_nat (length (mc_kept mc))) SL ->
  bytes_at rsegs mm (c + 8204 + 112 * Z.of_nat (length (mc_kept mc)) + 112) K2 ->
  bytes_at rsegs mm (c + 9132) (le4 (Z_to_bv 64 (Z.of_nat (length (mc_kept mc))))) ->
  bytes_at rsegs mm (c + 9136) Q3 ->
  rw_cells rsegs mm (bv_unsigned sp + -16) [C8 s0; C8 ra] ->
  wr_at rsegs mm c 9236 ->
  stk rsegs mm lo (bv_unsigned sp - 5952) ->
  munch [(bv_unsigned sp - 5952, bv_unsigned sp)] m mm -> wmono rsegs m mm ->
  munch [(bv_unsigned sp - 5952, bv_unsigned sp + -16);
         (c + 8204 + 112 * Z.of_nat (length (mc_kept mc)),
          c + 8204 + 112 * Z.of_nat (length (mc_kept mc)) + Z.of_nat (length txt) + 1)] mm mk ->
  wmono rsegs mm mk -> mem_inv rsegs mk ->
  stk rsegs mk (bv_unsigned sp - 5952) (bv_unsigned sp + -16) ->
  bytes_at rsegs mk (c + 8204 + 112 * Z.of_nat (length (mc_kept mc))) (zb txt ++ [ZERO]) ->
  frm0 fck -> (forall k : reg, bv_unsigned k <> 10 -> reg_get Fk k = reg_get F k) ->
  evt rsegs Post
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp y5 y6 y7 (Z_to_bv 64 (c + 8200)) s1
             z0 z1 z2 z3 z4 z5 z6 z7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
        Fk (Z_to_bv 64 0x14ff8) fck None mk (seg_rom rsegs)).
Proof.
  intros mm mk Fk fck x1 y5 y6 y7 z0 z1 z2 z3 z4 z5 z6 z7 u3 u4 u5 u6 Q1 K1 SL K2 Q3 txt
         HNK HMOD HTB HTL HE LQ1 LQ3 LK1 LSL LK2 BQ1 BR BK1 BSL0 BK2 BN BQ3 FR HW STlo MU WM
         MUc WMc MIk STk BTXT FRMk FEQk.
  nums.
  destruct (zsplit _ _ (Z.of_nat (length txt) + 1) _ BSL0 ltac:(lia))
    as (SLa & SLb & ESL & LSLa & BSLa & BSLb).
  assert (LSLb : Z.of_nat (length SLb) = 111 - Z.of_nat (length txt))
    by (subst SL; rewrite length_app in LSL; lia).
  eapply bytes_at_transport in BQ1; [| exact MUc | dj].
  eapply bytes_at_transport in BR; [| exact MUc | dj].
  eapply bytes_at_transport in BK1; [| exact MUc | dj].
  eapply bytes_at_transport in BSLb; [| exact MUc | dj].
  eapply bytes_at_transport in BK2; [| exact MUc | dj].
  eapply bytes_at_transport in BN; [| exact MUc | dj].
  eapply bytes_at_transport in BQ3; [| exact MUc | dj].
  eapply rw_cells_transport in FR; [| exact MUc | exact WMc | dj].
  eapply wr_at_transport in HW; [| exact WMc].
  eapply stk_transport_disjoint in STlo; [| exact MUc | exact WMc | dj].
  assert (CS : rw_cells rsegs mk (c + 8200)
                 [C4 (Z_to_bv 64 (mc_refused mc));
                  CB 928 (K1 ++ (zb txt ++ [ZERO] ++ SLb) ++ K2);
                  C4 (Z_to_bv 64 (Z.of_nat (length (mc_kept mc))))]).
  { apply mk_cells.
    - exact BR.
    - replace (c + 8200 + 4) with (c + 8204) by lia.
      apply (bytes_app2 _ (c + 8204) K1 ((zb txt ++ [ZERO] ++ SLb) ++ K2)
               (112 * Z.of_nat (length (mc_kept mc)))); [exact BK1 | | exact LK1].
      apply (bytes_app2 _ (c + 8204 + 112 * Z.of_nat (length (mc_kept mc)))
               (zb txt ++ [ZERO] ++ SLb) K2 112).
      + rewrite app_assoc.
        apply (bytes_app2 _ (c + 8204 + 112 * Z.of_nat (length (mc_kept mc)))
                 (zb txt ++ [ZERO]) SLb (Z.of_nat (length txt) + 1));
          [ exact BTXT | exact BSLb | rewrite length_app, length_zb; cbn [length]; lia ].
      + exact BK2.
      + rewrite !length_app, length_zb; cbn [length]; lia.
    - replace (c + 8200 + 932) with (c + 9132) by lia. exact BN.
    - rewrite !length_app, length_zb; cbn [length]; lia.
    - exact (wr_at_sub mk c 9236 8200 936 HW ltac:(lia) ltac:(lia) ltac:(lia)). }
  assert (MU' : munch [(bv_unsigned sp - 5952, bv_unsigned sp);
                       (c + 8204 + 112 * Z.of_nat (length (mc_kept mc)),
                        c + 8204 + 112 * Z.of_nat (length (mc_kept mc)) + 112);
                       (c + 9132, c + 9136); (c + 8200, c + 8204)] m mk).
  { eapply munch_trans;
      [ eapply munch_weaken; [| exact MU] | eapply munch_weaken; [| exact MUc] ];
      unfold sub_fp; intros xx Hxx; cbn [outside] in Hxx |- *; repeat split; first [exact I | lia]. }
  assert (ST' : stk rsegs mk lo (bv_unsigned sp + -16)).
  { apply (stk_merge rsegs mk lo (bv_unsigned sp - 5952) (bv_unsigned sp + -16));
      [exact STlo | exact STk | lia]. }
  eapply tail_kept with (Q1 := Q1) (K1 := K1) (SL := SL) (K2 := K2) (Q3 := Q3) (SLb := SLb) (txt := txt);
    [ lia | exact HMOD | exact HTB | exact HTL | exact FR | exact CS | exact BQ1 | exact LQ1 | exact BQ3
    | exact LQ3 | exact LK1 | exact LSL | exact LK2 | exact LSLb | exact HE | exact ST' | exact MIk
    | exact MU' | eapply wmono_trans; [exact WM | exact WMc] | exact FRMk | exact FEQk ].
Qed.

Lemma body : forall (t0 t1 t2 t3 t4 t5 t6 : word),
  evt rsegs Post
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 c) (Z_to_bv 64 ln) a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 M_REFUSE) fc None m (seg_rom rsegs)).
Proof.
  intros t0 t1 t2 t3 t4 t5 t6. unfold M_REFUSE.
  (* The steps below transport (and so replace) the section hypotheses these lemmas use: take them first. *)
  pose proof tail_full as TF. pose proof after_call as AC. pose proof env_after as EA.
  pose proof reading_str as RS. pose proof slot_noimg as SN. pose proof reading_pbyte as RP.
  nums.
  destruct HSLK as (sl & BSL & HSLm). unfold SEG_M_SIZE in BSL, HSLm.
  rewrite (slack_mod c Hc16) in HSLm.
  destruct (zsplit m (c + 9236) 4 sl BSL ltac:(lia)) as (SL4 & SLr & Esl & LSL4 & BSL4 & _).
  clear BSL.
  assert (Hcb : c + 9240 <= 2 ^ 64) by (pose proof (bytes_at_bound _ _ _ _ BSL4); lia).
  pose proof HW0 as HW1. unfold SEG_M_SIZE in HW1.
  (* the block's five pieces *)
  pose proof HB0 as HB1. pose proof HE0 as HE1.
  destruct (zsplit m c 8200 bs HB1 ltac:(lia)) as (Q1 & T1 & Ebs & LQ1 & BQ1 & BT1).
  rewrite Ebs in HE1, HLb, Hrefd, Hnk, Hrd. clear HB1. rewrite length_app in HLb.
  destruct (zsplit m (c + 8200) 4 T1 BT1 ltac:(lia)) as (R & T2 & ET1 & LR & BR & BT2).
  subst T1. rewrite length_app in HLb.
  destruct (zsplit m (c + 8200 + 4) 928 T2 BT2 ltac:(lia)) as (MID & T3 & ET2 & LMID & BMID & BT3).
  subst T2. rewrite length_app in HLb.
  destruct (zsplit m (c + 8200 + 4 + 928) 4 T3 BT3 ltac:(lia)) as (N & Q3 & ET3 & LN & BN & BQ3).
  subst T3. rewrite length_app in HLb.
  replace (c + 8200 + 4) with (c + 8204) in BMID by lia.
  replace (c + 8200 + 4 + 928) with (c + 9132) in BN by lia.
  replace (c + 8200 + 4 + 928 + 4) with (c + 9136) in BQ3 by lia.
  assert (LQ3 : Z.of_nat (length Q3) = 100) by lia.
  assert (ER : R = le4 (Z_to_bv 64 (mc_refused mc))).
  { pose proof (proj2 Hrefd) as HR. revert HR. unfold fldz, MC_REFUSED. fsimp.
    rewrite fld_full by flen. intros HR. exact HR. }
  assert (EN : N = le4 (Z_to_bv 64 (Z.of_nat (length (mc_kept mc))))).
  { pose proof (proj2 Hnk) as HR. revert HR. unfold fldz, MC_NKEPT. fsimp.
    rewrite fld_full by flen. intros HR. exact HR. }
  subst R N.
  (* the reading field: the last 96 bytes of Q3 *)
  destruct (zsplit m (c + 9136) 4 Q3 BQ3 ltac:(lia)) as (G & RD & EQ3 & LG & BG & BRD).
  replace (c + 9136 + 4) with (c + 9140) in BRD by lia.
  assert (LRD : Z.of_nat (length RD) = 96) by (subst Q3; rewrite length_app in LQ3; lia).
  assert (HRD : cstr_enc 96 (mc_reading mc) RD).
  { pose proof Hrd as HR. revert HR. unfold fldz, MC_READING. subst Q3. fsimp.
    rewrite fld_full by flen. intros HR. exact HR. }
  (* the prologue *)
  pose proof (munch_refl [(bv_unsigned sp - 5952, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 16%nat ST0.
  zstep. zstep. zstep.
  (* the cells of refused .. n_kept *)
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (CS : rw_cells rsegs mm (c + 8200)
                     [C4 (Z_to_bv 64 (mc_refused mc)); CB 928 MID;
                      C4 (Z_to_bv 64 (Z.of_nat (length (mc_kept mc))))]);
      [ apply mk_cells;
        [ exact BR | replace (c + 8200 + 4) with (c + 8204) by lia; exact BMID
        | replace (c + 8200 + 932) with (c + 9132) by lia; exact BN
        | exact LMID
        | exact (wr_at_sub mm c 9236 8200 936 HW1 ltac:(lia) ltac:(lia) ltac:(lia)) ] | ]
  end.
  (* 0x14f3c andi a2,a0,3; bnez a2 -> trap: c is 16-aligned *)
  assert (HL3 : Z.land c 3 = 0).
  { change 3 with (Z.ones 2). rewrite Z.land_ones by lia. change (2 ^ 2) with 4.
    Z.div_mod_to_equations; lia. }
  zstep. zstep.
  if_cases KA; zify_cond KA.
  { exfalso. rewrite ?unsigned_lit in KA by lia. lia. }
  (* 0x14f44 mv a4,a1; s0 = c + 0x2008; lw a1,0x3a4(s0) *)
  zstep. zstep. zstep. zstep. zstep.
  rewrite sx32_small by lia.
  (* addi a2,zero,7; blt a2,a1 *)
  zstep. zstep.
  if_cases K1; zify_cond K1; rewrite signed_small in K1 by lia.
  - (* n_kept = 8 *)
    lazymatch goal with
    | |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        assert (MU8 : munch [(bv_unsigned sp - 5952, bv_unsigned sp); (c + 8200, c + 8204)] m mm)
          by (eapply munch_weaken; [| exact MU]; unfold sub_fp; intros xx Hxx;
              cbn [outside] in Hxx |- *; repeat split; first [exact I | lia])
    end.
    assert (FEQ0 : forall k : reg, bv_unsigned k <> 10 -> reg_get F k = reg_get F k) by (intros; reflexivity).
    eapply TF with (Q1 := Q1) (MID := MID) (Q3 := Q3); first [eassumption | lia].
  - (* n_kept <= 7: the slot and the two calls *)
    assert (HNK : 0 <= Z.of_nat (length (mc_kept mc)) <= 7) by lia.
    destruct (zsplit _ _ (112 * Z.of_nat (length (mc_kept mc))) _ BMID ltac:(lia))
      as (K1a & MT & EMID & LK1a & BK1a & BMT).
    assert (LMT : Z.of_nat (length MT) = 928 - 112 * Z.of_nat (length (mc_kept mc)))
      by (subst MID; rewrite length_app in LMID; lia).
    destruct (zsplit _ _ 112 _ BMT ltac:(lia)) as (SL & K2a & EMT & LSL & BSL0 & BK2a).
    assert (LK2a : Z.of_nat (length K2a) = 816 - 112 * Z.of_nat (length (mc_kept mc))).
    { subst MT. rewrite length_app in LMT. lia. }
    lazymatch goal with
    | |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        assert (WSLOT : wr_at rsegs mm (c + 8204 + 112 * Z.of_nat (length (mc_kept mc))) 112);
        [ replace (c + 8204 + 112 * Z.of_nat (length (mc_kept mc)))
            with (c + (8204 + 112 * Z.of_nat (length (mc_kept mc)))) by lia;
          apply (wr_at_sub mm c 9236); [exact HW1 | lia | lia | lia] | ]
    end.
    subst MID MT.
    destruct (stk_split rsegs _ lo (bv_unsigned sp - 5952) (bv_unsigned sp + -16) ST0 ltac:(lia))
      as [STlo SThi].
    (* 0x14f60 blez a4 *)
    zstep.
    if_cases K2; zify_cond K2.
    + (* line = 0: snprintf(&kept[n], 112, "%s: ", c->reading) *)
      assert (Eln : ln = 0).
      { apply andb_false_iff in K2; destruct K2 as [K|K]; apply Z.ltb_ge in K; lia. }
      (* 0x14fb0 addi a2,zero,8; bltu a2,a1 -> trap (n_kept <= 7) *)
      zstep. zstep.
      if_cases KB; zify_cond KB.
      { exfalso. rewrite ?unsigned_lit in KB by lia. lia. }
      (* 0x14fb8 lui; slli; slli; addiw; add; sub; not a3,a4; bltu a3,a1 -> trap (no wrap) *)
      zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
      if_cases KW; zify_cond KW.
      { exfalso. rewrite ?unsigned_lit in KW by lia. rewrite ?Z.shiftl_mul_pow2 in KW by lia.
        rewrite ?Z.mod_small in KW by lia. rewrite ?zb_lxor_ones in KW by lia. lia. }
      (* 0x14fd8 .. 0x14ff4: the slot, the reading, the format, 112; jal snprintf *)
      zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
      fix_slot.
      eapply evt_cut.
      { eapply HSN with (lo := bv_unsigned sp - 5952) (junk := SL) (rd := mc_reading mc) (line := ln)
                        (f := F_addr) (args := [AS (mc_reading mc)]).
        - right. split; [reflexivity|]. split; [reflexivity|].
          rewrite unsigned_lit by lia. reflexivity.
        - rewrite unsigned_lit by lia. apply fmt_a_bytes. assumption.
        - rewrite !unsigned_lit by lia.
          eapply RS; [exact BRD | exact HRD | exact BSL4 | lia | lia | lia].
        - lia.
        - rewrite !unsigned_lit by lia. apply mk_cb; [exact BSL0 | exact LSL | exact WSLOT].
        - rewrite unsigned_lit by lia. lia.
        - rewrite unsigned_lit by lia. lia.
        - rewrite !unsigned_lit by lia. lia.
        - rewrite !unsigned_lit by lia.
          replace (c + 8204 + 112 * Z.of_nat (length (mc_kept mc)))
            with (c + (8204 + 112 * Z.of_nat (length (mc_kept mc)))) by lia.
          apply SN; lia.
        - rewrite unsigned_lit by lia. exact SThi.
        - rewrite unsigned_lit by lia. unfold PRINTF_K. lia.
        - rewrite unsigned_lit by lia. apply EA. exact MU.
        - assumption. }
      intros ms' PO. unfold mr_post, ret_post_fp in PO.
      destruct PO as (y0 & y1 & y2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & Fk & fck & mk &
                      -> & FRMk & FEQk & MUc & WMc & MIk & TMk & STk & BTXT).
      rewrite ret_pc_even by (try lia; reflexivity).
      rewrite !unsigned_lit in MUc, BTXT, STk by lia.
      assert (HMOD : m_refuse mc ln knock =
                     MConf (mc_seg mc) (mc_overflow mc) (mc_refused mc + 1)
                       (mc_kept mc ++ [(snprintf_s 112 F_addr [AS (mc_reading mc)], knock)])
                       (mc_gen mc) (mc_reading mc)).
      { unfold m_refuse. cbv zeta.
        replace (Z.of_nat (length (mc_kept mc)) <? 8) with true by (symmetry; apply Z.ltb_lt; lia).
        replace (0 <? ln) with false by (symmetry; apply Z.ltb_ge; lia).
        reflexivity. }
      assert (HTB : Forall pbyte (snprintf_s 112 F_addr [AS (mc_reading mc)])).
      { unfold snprintf_s. apply Forall_firstn_gen. apply fmt_a_pbyte. exact (RP RD HRD). }
      pose proof (snprintf_len F_addr [AS (mc_reading mc)]) as HTL.
      eapply (AC _ mk Fk fck) with (Q1 := Q1) (K1 := K1a) (SL := SL) (K2 := K2a) (Q3 := Q3)
        (txt := snprintf_s 112 F_addr [AS (mc_reading mc)]); try eassumption; try lia.
      rewrite (unsigned_lit (c + 8204 + 112 * Z.of_nat (length (mc_kept mc)))) in MUc by lia.
      rewrite (unsigned_lit 112) in MUc by lia.
      exact MUc.
    + (* line > 0: snprintf(&kept[n], 112, "%s:%d: ", c->reading, line) *)
      (* 0x14f64 addi a2,zero,9; bgeu a1,a2 -> trap (n_kept <= 7) *)
      zstep. zstep.
      if_cases KB; zify_cond KB.
      { exfalso. rewrite ?unsigned_lit in KB by lia. lia. }
      (* 0x14f6c lui; slli; slli; addiw; add; sub; not a3,a5; bltu a3,a1 -> trap (no wrap) *)
      zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
      if_cases KW; zify_cond KW.
      { exfalso. rewrite ?unsigned_lit in KW by lia. rewrite ?Z.shiftl_mul_pow2 in KW by lia.
        rewrite ?Z.mod_small in KW by lia. rewrite ?zb_lxor_ones in KW by lia. lia. }
      (* 0x14f8c .. 0x14fa8: the slot, the reading, the format, 112; jal snprintf *)
      zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
      fix_slot.
      eapply evt_cut.
      { eapply HSN with (lo := bv_unsigned sp - 5952) (junk := SL) (rd := mc_reading mc) (line := ln)
                        (f := F_addr_line) (args := [AS (mc_reading mc); AI ln]).
        - left. split; [reflexivity|]. split; [reflexivity|].
          split; [rewrite unsigned_lit by lia; reflexivity|].
          split; [rewrite unsigned_lit by lia; reflexivity | lia].
        - rewrite unsigned_lit by lia. apply fmt_al_bytes. assumption.
        - rewrite !unsigned_lit by lia.
          eapply RS; [exact BRD | exact HRD | exact BSL4 | lia | lia | lia].
        - lia.
        - rewrite !unsigned_lit by lia. apply mk_cb; [exact BSL0 | exact LSL | exact WSLOT].
        - rewrite unsigned_lit by lia. lia.
        - rewrite unsigned_lit by lia. lia.
        - rewrite !unsigned_lit by lia. lia.
        - rewrite !unsigned_lit by lia.
          replace (c + 8204 + 112 * Z.of_nat (length (mc_kept mc)))
            with (c + (8204 + 112 * Z.of_nat (length (mc_kept mc)))) by lia.
          apply SN; lia.
        - rewrite unsigned_lit by lia. exact SThi.
        - rewrite unsigned_lit by lia. unfold PRINTF_K. lia.
        - rewrite unsigned_lit by lia. apply EA. exact MU.
        - assumption. }
      intros ms' PO. unfold mr_post, ret_post_fp in PO.
      destruct PO as (y0 & y1 & y2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & Fk & fck & mk &
                      -> & FRMk & FEQk & MUc & WMc & MIk & TMk & STk & BTXT).
      rewrite ret_pc_even by (try lia; reflexivity).
      rewrite !unsigned_lit in MUc, BTXT, STk by lia.
      zstep.
      assert (HMOD : m_refuse mc ln knock =
                     MConf (mc_seg mc) (mc_overflow mc) (mc_refused mc + 1)
                       (mc_kept mc ++ [(snprintf_s 112 F_addr_line [AS (mc_reading mc); AI ln], knock)])
                       (mc_gen mc) (mc_reading mc)).
      { unfold m_refuse. cbv zeta.
        replace (Z.of_nat (length (mc_kept mc)) <? 8) with true by (symmetry; apply Z.ltb_lt; lia).
        replace (0 <? ln) with true by (symmetry; apply Z.ltb_lt; lia).
        reflexivity. }
      assert (HTB : Forall pbyte (snprintf_s 112 F_addr_line [AS (mc_reading mc); AI ln])).
      { unfold snprintf_s. apply Forall_firstn_gen. apply fmt_al_pbyte. exact (RP RD HRD). }
      pose proof (snprintf_len F_addr_line [AS (mc_reading mc); AI ln]) as HTL.
      eapply (AC _ mk Fk fck) with (Q1 := Q1) (K1 := K1a) (SL := SL) (K2 := K2a) (Q3 := Q3)
        (txt := snprintf_s 112 F_addr_line [AS (mc_reading mc); AI ln]); try eassumption; try lia.
      rewrite (unsigned_lit (c + 8204 + 112 * Z.of_nat (length (mc_kept mc)))) in MUc by lia.
      rewrite (unsigned_lit 112) in MUc by lia.
      exact MUc.
Qed.

End W.

Theorem m_refuse_holds : snprintf_m_contract -> m_refuse_contract.
Proof.
  intros HM. pose proof (mr_snprintf_of_m HM) as HSN.
  unfold m_refuse_contract, m_refuse_pre.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         F fc m lo mc knock
         (Hc0 & Hc16 & Himg & (bs & HB & HE) & HW & HSL & Hap & Hln & Hrf & HENV & HST & MI).
  pose proof (Z_to_bv_bv_unsigned a0) as Ea0. pose proof (Z_to_bv_bv_unsigned a1) as Ea1.
  set (c := bv_unsigned a0) in *. set (ln := bv_unsigned a1) in *.
  rewrite <- Ea0, <- Ea1. clearbody c ln. clear Ea0 Ea1.
  eapply body; eassumption.
Qed.
