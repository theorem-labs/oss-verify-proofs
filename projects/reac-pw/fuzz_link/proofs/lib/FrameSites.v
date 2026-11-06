From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Fs Require Namei.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
  YK11 YK0s YK15 YM06 YP09 YO0i YO0f YO0d YI06 YI16 YI00 YI14 YI5b YI5c YH00 YH02 YM05 YL0g YL0i YL0k YL06 YL0t.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM02 YO05 YO09 YO06 YO04.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require Import
  TraceHalting ZTraceSpec AllocSlots AllocRoom Contract SlotKept SlotPack MemFileSink MemFile MemFileRI StdioExitMF.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import DriverSlots.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

Section Sites.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

Lemma site_pre_mf_sink_first : forall (B : malloc_syms) {SH : sink_head} {SK : sink_syms} mem md,
  sink_none B mem md ->
  word_mem (ms_segs B) mem (mf_sink_addr link_mf) 0 -> word_mem (ms_segs B) mem (mf_say_addr link_mf) 0 ->
  @mf_sink B SH SK link_mf mem md.
Proof. intros B SH SK mem md H Hs Hy. exact (mf_sink_of_none B link_mf mem md H Hs Hy). Qed.

Lemma site_pre_mf_sink_later : forall T mem md,
  mf_gi src0_msyms link_mf T mem -> closed_stdio_env src0_msyms mem ->
  Namei.fd_names_path (m_fds md) sink_path = false ->
  @mf_sink src0_msyms src0_sink_head src0_sink link_mf mem md.
Proof. intros T mem md H He Hn. exact (mf_sink_of_gi_site T mem md H He Hn). Qed.

Lemma site_post_names : forall (B : malloc_syms) {SH : sink_head} {SK : sink_syms} mem md,
  @mf_sink B SH SK link_mf mem md -> Namei.fd_names_path (m_fds md) sink_path = false.
Proof. intros B SH SK mem md H. exact (mf_sink_names B link_mf mem md H). Qed.

Lemma site_post_env : forall (B : malloc_syms) {SH : sink_head} {SK : sink_syms} mem md,
  @mf_sink B SH SK link_mf mem md -> closed_stdio_env B mem.
Proof. intros B SH SK mem md H. exact (mf_sink_env B link_mf mem md H). Qed.

Lemma site_post_is_sink_none_when_closed : forall (B : malloc_syms) {SH : sink_head} {SK : sink_syms} mem md,
  @mf_sink B SH SK link_mf mem md -> mf_heads B link_mf mem 0 -> sink_none B mem md.
Proof. intros B SH SK mem md H H0. exact (mf_none_of_sink B link_mf mem md H H0). Qed.

Lemma site_carry_local : G_local_T src0segs src0_G mf_GI.
Proof. exact mf_GI_local. Qed.

Lemma site_carry_free : forall j T L A L' A' p n m m',
  mf_GI j T m -> tb_live L A T -> ~ In (ptr_addr L p, n) T -> In (p, n) (user_blocks A) ->
  pairwise ranges_disjoint (blocks L A) -> 0 < n ->
  (forall a, in_globals src0_G a -> mbyte src0segs m' a = mbyte src0segs m a) ->
  (forall q sz i, In (q, sz) (user_blocks A) -> q <> p -> 0 <= i < sz ->
     mbyte src0segs m' (ptr_addr L q + i) = mbyte src0segs m (ptr_addr L q + i)) ->
  (forall q sz, In (q, sz) (user_blocks A) -> q <> p -> In (q, sz) (user_blocks A') /\ ptr_addr L' q = ptr_addr L q) ->
  mf_GI j T m' /\ tb_live L' A' T.
Proof. exact mf_gi_after_free. Qed.

Lemma site_exit_head : forall T mem,
  mf_gi src0_msyms link_mf T mem ->
  (word_mem src0segs mem (@sk_ofl_head src0_sink_head) 0 /\ T = []) \/
  (exists f, word_mem src0segs mem (@sk_ofl_head src0_sink_head) f /\ T = [(f, MF_BLOCK)] /\
     memfile_at src0_msyms link_mf mem f).
Proof.
  intros T mem [(H & HT) | (f & Hf & HT & Hm)].
  - left. split; [exact (mf_heads_ofl src0_msyms link_mf mem 0 H) | exact HT].
  - right. exists f. split; [exact (mf_heads_ofl src0_msyms link_mf mem f Hf)|]. split; [exact HT | exact Hm].
Qed.

Lemma site_exit_block : forall T mem L A f,
  mf_gi src0_msyms link_mf T mem -> tb_live L A T -> mf_heads src0_msyms link_mf mem f ->
  memfile_at src0_msyms link_mf mem f -> T = [(f, MF_BLOCK)] -> In (f, MF_BLOCK) (blocks L A).
Proof. intros T mem L A f _ [_ HTL] _ _ ->. apply HTL. left. reflexivity. Qed.

Lemma site_exit_reads : forall mem f, memfile_at src0_msyms link_mf mem f ->
  val_mem src0segs mem (f + 140) 4 U32M1 /\ val_mem src0segs mem (f + 72) 8 (mf_write link_mf) /\
  val_mem src0segs mem (f + 8) 8 0 /\ val_mem src0segs mem (f + 16) 8 0 /\ val_mem src0segs mem (f + 112) 8 0.
Proof. intros mem f H. exact (memfile_close_reads src0_msyms link_mf mem f H). Qed.

Lemma site_RI_step : forall (GI : nat -> list (Z * Z) -> (word -> option byte) -> Prop),
  (forall j T m, GI j T m -> mf_gi src0_msyms link_mf T m) ->
  forall j, (j < 4)%nat -> forall pl T A m, RI_mf pl j T A -> GI j T m ->
  exists b, res_ok_slots A b /\ @lib_room mf_shape b (Z.of_nat (length pl)) /\
  forall T' A' m', res_ok_slots A' (TD T T' (@lib_delta mf_shape (Z.of_nat (length pl)) b)) ->
    GI (S j) T' m' -> RI_mf pl (S j) T' A'.
Proof. intros GI H. exact (RI_mf_step src0_msyms link_mf GI H). Qed.

Lemma site_RI_driver : forall data, leaves (run_RI RI_mf (payload data)) (driver_tree data).
Proof. exact driver_RI_mf. Qed.

Lemma site_TD_open : forall f b, TD [] [(f, MF_BLOCK)] b = sb_malloc b MF_BLOCK.
Proof. exact mf_TD_open. Qed.
Lemma site_TD_keep : forall f b, TD [(f, MF_BLOCK)] [(f, MF_BLOCK)] b = b.
Proof. exact mf_TD_keep. Qed.

Lemma site_G_covers_heads : forall a, @mf_head_addr src0_sink_head link_mf a -> in_globals src0_G a.
Proof. exact mf_head_in_G. Qed.

Lemma site_G_covers_said : forall a, mf_said_addr link_mf a -> in_globals src0_G a.
Proof.
  intros a Ha. cbv [mf_said_addr mf_buf mf_size link_mf] in Ha. unfold in_globals, src0_G.
  exists 0x74530, 4096. split; [cbn; tauto | lia].
Qed.

Lemma site_room : forall b, @lib_room mf_shape b 0 -> sb_live b + 1 <= 64 -> sb_bytes b + MF_BLOCK <= 2 ^ 40 ->
  room_slots b MF_BLOCK.
Proof. exact mf_shape_room_file. Qed.

End Sites.
