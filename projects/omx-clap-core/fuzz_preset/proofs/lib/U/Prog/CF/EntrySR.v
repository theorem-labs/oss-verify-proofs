From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import Contract Img0 FrameAPI SlotPack.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjRoundTrip.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import PjStruct.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import WriterSpec WriterApp WriterValue.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF Require Import WriterRet.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import LLVMFuzzerTestOneInput_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF Require Import pj_parse_c check_no_overread_c check_reject_clean_starved_c round_trip_text_c check_round_trip_c EntryDefs.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF Require Import SRCF.
Import ListNotations.
Local Open Scope Z_scope.

Section R.
Variable F : ResForm.

Definition crt_pre_rooms (b : rf_R F) (cnt : Z) (t : jv) : Prop :=
  rtt_rooms F b cnt t false /\ rtt_rooms F (crt_b1 F b cnt t) (crt_cnt1 cnt t) t true /\
  (forall ms, t = JObj ms -> forall Df, crt_dl (PjRoundTrip.ttrace t) Df ->
     crt_obj_rooms F (crt_b2 F b cnt t Df) (crt_cnt2 cnt t) t (Z.of_nat (length ms))).

Definition crs_rooms (b : rf_R F) (cnt : Z) (x : list byte) (doc : Z) (t : jv) : Prop :=
  (ent_took x <> 0 -> room_run F b (ent_T x)) /\
  (ent_took x = 0 -> doc <> 0 -> crs_doc_rooms F b cnt (zb x) t) /\
  (ent_took x <> 0 -> doc <> 0 -> forall tr D', crs_parse_left cnt (zb x) (ent_took x) tr D' ->
     crs_doc_rooms F (rf_frees F (rf_run F b tr) D') (cnt + Z.of_nat (calls tr)) (zb x) t).

Definition ent_c4 (cnt0 : Z) (x : list byte) (t : jv) (cset : Z) : Z := ent_c3 cnt0 x + crt_count t cset.

Definition ent_b5 (b4 : rf_R F) (c4 : Z) (x : list byte) (t : jv) (trs : list ev) (Ds : list (Z * Z)) : rf_R F :=
  if ent_took x =? 0 then crs_doc_fold F b4 c4 (zb x) t
  else crs_doc_fold F (rf_frees F (rf_run F b4 trs) Ds) (c4 + Z.of_nat (calls trs)) (zb x) t.

Definition entry_rooms (b0 : rf_R F) (cnt0 : Z) (x : list byte) : Prop :=
  ent_n x <= 0x300000 ->
  cno_room F b0 (ent_n x) (ent_T x) (cno_ok x) /\
  forall E1 E2 E3, cno_dl (ent_T x) E1 -> cno_dl (ent_T x) E2 -> cno_dl (ent_T x) E3 ->
  room_run F (ent_b1 F b0 x E1 E2 E3) (ent_T x) /\
  match json_read jr_strtod (zb x) with
  | None =>
      forall D Dp, Permutation D Dp -> ent_tree_dl x D ->
      rf_room F (ent_b2 F b0 x E1 E2 E3 Dp) (ent_n x + 1) /\
      crs_rooms (ent_b3 F b0 x E1 E2 E3 Dp) (ent_c3 cnt0 x) x 0 JNull
  | Some t =>
      rf_room F (ent_b2 F b0 x E1 E2 E3 []) (ent_n x + 1) /\
      crt_pre_rooms (ent_b3 F b0 x E1 E2 E3 []) (ent_c3 cnt0 x) t /\
      forall cset b4, crt_fin F (ent_b3 F b0 x E1 E2 E3 []) (ent_c3 cnt0 x) t cset b4 ->
      crs_rooms b4 (ent_c4 cnt0 x t cset) x 1 t
  end.

Definition entry_wit (b0 : rf_R F) (cnt0 : Z) (x : list byte) (E1 E2 E3 Dp : list (Z * Z)) (cset : Z) (b4 : rf_R F)
    (trs : list ev) (Ds Df : list (Z * Z)) : Prop :=
  ent_n x <= 0x300000 ->
  cno_dl (ent_T x) E1 /\ cno_dl (ent_T x) E2 /\ cno_dl (ent_T x) E3 /\
  match json_read jr_strtod (zb x) with
  | None =>
      (exists D, Permutation D Dp /\ ent_tree_dl x D) /\
      (ent_took x <> 0 -> crs_parse_left (ent_c3 cnt0 x) (zb x) (ent_took x) trs Ds)
  | Some t =>
      crt_fin F (ent_b3 F b0 x E1 E2 E3 []) (ent_c3 cnt0 x) t cset b4 /\
      (ent_took x <> 0 -> crs_parse_left (ent_c4 cnt0 x t cset) (zb x) (ent_took x) trs Ds) /\
      (exists D, Permutation D Df /\ ent_tree_dl x D)
  end.

Definition entry_fold (b0 : rf_R F) (cnt0 : Z) (x : list byte) (E1 E2 E3 Dp : list (Z * Z)) (cset : Z)
    (b4 : rf_R F) (trs : list ev) (Ds Df : list (Z * Z)) : rf_R F :=
  if 0x300000 <? ent_n x then b0 else
  match json_read jr_strtod (zb x) with
  | None => ent_brej F b0 x E1 E2 E3 Dp trs Ds
  | Some t => rf_frees F (ent_b5 b4 (ent_c4 cnt0 x t cset) x t trs Ds) Df
  end.

End R.

Inductive ent_dem : Type :=
| DM (n : Z)
| DR (T : list ev)
| DCno (n : Z) (T : list ev) (ok : bool)
| DCrt (cnt : Z) (t : jv)
| DCrs (cnt : Z) (x : list byte) (doc : Z) (t : jv).

Section D.
Variable F : ResForm.

Definition dem_ok (bd : rf_R F * ent_dem) : Prop :=
  match snd bd with
  | DM n => rf_room F (fst bd) n
  | DR T => room_run F (fst bd) T
  | DCno n T ok => cno_room F (fst bd) n T ok
  | DCrt c t => crt_pre_rooms F (fst bd) c t
  | DCrs c x doc t => crs_rooms F (fst bd) c x doc t
  end.

Definition entry_demands (b0 : rf_R F) (cnt0 : Z) (x : list byte) (E1 E2 E3 Dp : list (Z * Z)) (cset : Z)
    (b4 : rf_R F) : list (rf_R F * ent_dem) :=
  if 0x300000 <? ent_n x then [] else
  [(b0, DCno (ent_n x) (ent_T x) (cno_ok x)); (ent_b1 F b0 x E1 E2 E3, DR (ent_T x))] ++
  match json_read jr_strtod (zb x) with
  | None => [(ent_b2 F b0 x E1 E2 E3 Dp, DM (ent_n x + 1)); (ent_b3 F b0 x E1 E2 E3 Dp, DCrs (ent_c3 cnt0 x) x 0 JNull)]
  | Some t => [(ent_b2 F b0 x E1 E2 E3 [], DM (ent_n x + 1)); (ent_b3 F b0 x E1 E2 E3 [], DCrt (ent_c3 cnt0 x) t);
               (b4, DCrs (ent_c4 cnt0 x t cset) x 1 t)]
  end.

Lemma entry_rooms_demands : forall b0 cnt0 x E1 E2 E3 Dp cset b4 trs Ds Df,
  entry_rooms F b0 cnt0 x -> entry_wit F b0 cnt0 x E1 E2 E3 Dp cset b4 trs Ds Df ->
  Forall dem_ok (entry_demands b0 cnt0 x E1 E2 E3 Dp cset b4).
Proof.
  intros b0 cnt0 x E1 E2 E3 Dp cset b4 trs Ds Df HR HW. unfold entry_demands.
  destruct (0x300000 <? ent_n x) eqn:Hb; [constructor|].
  apply Z.ltb_ge in Hb. destruct (HR Hb) as (HC & HN).
  destruct (HW Hb) as (W1 & W2 & W3 & W).
  destruct (HN E1 E2 E3 W1 W2 W3) as (HR1 & HM).
  destruct (json_read jr_strtod (zb x)) as [t|] eqn:Ej; cbn [app].
  - destruct HM as (HM1 & HM2 & HM3). destruct W as (WF & _ & _).
    repeat (apply Forall_cons; [unfold dem_ok; cbn [fst snd]; eauto |]); apply Forall_nil.
  - destruct W as ((D & HP & HD) & _). destruct (HM D Dp HP HD) as (HM1 & HM2).
    repeat (apply Forall_cons; [unfold dem_ok; cbn [fst snd]; eauto |]); apply Forall_nil.
Qed.

End D.

Section K.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Variable F : ResForm.
Let segs := ms_segs B.
Let MR := aa_MR API.

Definition ent_post (stk : Z) (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
    (p n : Z) (l : lleaf) (L' : layout) (A' : astate) (regs' : bvmap 5 word) (mem' : word -> option byte)
    (md' : Model) : Prop :=
  MR L' A' mem' md' /\ WF A' /\ bounded A' /\ st_init_done A' = true /\
  getr regs' 10 = Z_to_bv 64 0 /\
  regs_preserved regs regs' /\
  (exists vm' fds' pins', md' = os_upd vm' fds' (ll_fs l) pins' md /\ forall k, fd_lookup fds' k = fd_lookup (m_fds md) k) /\
  (forall q k, In (q, k) (user_blocks A) -> exists q', In (q', k) (user_blocks A') /\ ptr_addr L' q' = ptr_addr L q) /\
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ lib_scratch B stk regs a ->
     mbyte segs mem' a = mbyte segs mem a /\ (writable_at segs mem a <-> writable_at segs mem' a)) /\
  (forall a, in_img B a -> ~ static_owned B a -> ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) ->
     ~ (errno_addr B <= a < errno_addr B + 4) -> ~ in_globals slot_G a ->
     mbyte segs mem' a = mbyte segs mem a /\ (writable_at segs mem a <-> writable_at segs mem' a)) /\
  (forall a, in_globals slot_G a -> writable_at segs mem a <-> writable_at segs mem' a) /\
  (forall q k i, In (q, k) (user_blocks A) -> ptr_addr L q <> p -> 0 <= i < k ->
     mbyte segs mem' (ptr_addr L q + i) = mbyte segs mem (ptr_addr L q + i)) /\
  (forall a, lib_scratch B stk regs a -> writable_at segs mem' a) /\
  ll_ret l = 0 /\ ll_out l = [] /\ Fs.fs_sorted (ll_fs l) = true /\
  sink_none B mem' md' /\
  ro_agree segs mem' /\
  (forall i, 0 <= i < n -> mbyte segs mem' (p + i) = mbyte segs mem (p + i)).

Definition entry_sr_contract (ra empty stk : Z) : Prop :=
  slot_syms B -> slot_globals B -> slot_sinks B -> ra mod 2 = 0 -> 0 < empty < 2 ^ 62 -> empty = 0x35230 ->
  SLOT_K <= stk ->
  forall (j : nat) L A regs mem md p n pl (peak cnt : Z) (b0 : rf_R F),
    (j < 4)%nat ->
    lib_pre_w B API stk empty L A regs mem md ra p n pl ->
    G_img_c B frame_RELRO mem -> ro_agree segs mem -> spZ regs <= TASK_SIZE -> frm_zero fp_csr ->
    ledger B L A mem [] peak cnt (2 ^ 64 - 1) -> cnt <= Z.of_nat j * 2 ^ 60 ->
    rf_ok F A b0 -> entry_rooms F b0 cnt pl ->
    SR segs (mkCfg (mkst regs (Z_to_bv 64 LLVMFUZZERTESTONEINPUT) mem (seg_rom segs)) md)
      (fun c' => exists (fx' : YK11.FPState) L' A' regs' mem' md' E1 E2 E3 Dp cset b4 trs Ds Df,
         c' = mkCfg (@mkst fx' regs' (Z_to_bv 64 ra) mem' (seg_rom segs)) md' /\
         frm_zero (@fp_csr fx') /\
         ent_post stk L A regs mem md p n (LL 0 (m_fs md) []) L' A' regs' mem' md' /\
         omx_GI B (S j) mem' /\
         entry_wit F b0 cnt pl E1 E2 E3 Dp cset b4 trs Ds Df /\
         rf_ok F A' (entry_fold F b0 cnt pl E1 E2 E3 Dp cset b4 trs Ds Df)).

End K.
