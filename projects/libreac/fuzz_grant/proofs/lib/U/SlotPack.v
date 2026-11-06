From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09 PlaceCap.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U Require Import Contract AllocPack SlotKept.
Import ListNotations.
Local Open Scope Z_scope.

Definition TDP (T T' : list (Z * Z)) (b : pbound) : pbound :=
  fold_left (fun b t => pb_malloc b (snd t)) T' (fold_left (fun b t => pb_free b (snd t)) T b).

Definition PCAP0 : Z := 64.
Definition PDRV_LIVE : Z := 2.
Definition PDRV_BYTES : Z := 2 ^ 28.

Definition drv_pb (d : pbound) : Prop :=
  length (pb_live d) = 49%nat /\ (forall k, 0 <= k < 49 -> 0 <= znth k (pb_live d)) /\
  zsumZ (fun k => znth k (pb_live d)) (zseq 0 49) <= PDRV_LIVE /\ 0 <= pb_bytes d <= PDRV_BYTES.

Definition CS_ok (CS : list byte -> list Z) : Prop :=
  forall x, length (CS x) = 49%nat /\ forall k, 0 <= k < 49 -> PCAP0 <= znth k (CS x).

Definition pack_entry (CS : list byte -> list Z) (pl : list byte) (T : list (Z * Z)) (b : pbound) : Prop :=
  length (pb_cap b) = 49%nat /\ (forall k, 0 <= k < 49 -> PCAP0 <= znth k (pb_cap b) <= znth k (CS pl)) /\
  exists d, drv_pb d /\ pb_live b = pb_live (TDP [] T d) /\ pb_bytes b = pb_bytes (TDP [] T d).

Section Pack.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Let segs := ms_segs B.
Let MR := aa_MR API.

Definition lib_post_p (cs : list Z) (G : list (Z * Z)) (stk : Z) (L : layout) (A : astate) (regs : bvmap 5 word)
    (mem : word -> option byte) (md : Model) (p n : Z) (b : pbound) (l : lleaf) (T T' : list (Z * Z))
    (L' : layout) (A' : astate) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) : Prop :=
  MR L' A' mem' md' /\ WF A' /\ bounded A' /\ st_init_done A' = true /\
  getr regs' 10 = Z_to_bv 64 0 /\
  regs_preserved regs regs' /\
  (exists vm' fds' pins', md' = os_upd vm' fds' (ll_fs l) pins' md /\ forall k, fd_lookup fds' k = fd_lookup (m_fds md) k) /\
  (forall q k, In (q, k) (user_blocks A) -> ~ In (ptr_addr L q, k) T ->
     exists q', In (q', k) (user_blocks A') /\ ptr_addr L' q' = ptr_addr L q) /\
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ lib_scratch B stk regs a ->
     mbyte segs mem' a = mbyte segs mem a /\ (writable_at segs mem a <-> writable_at segs mem' a)) /\
  (forall a, in_img B a -> ~ static_owned B a -> ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) ->
     ~ (errno_addr B <= a < errno_addr B + 4) -> ~ in_globals G a ->
     mbyte segs mem' a = mbyte segs mem a /\ (writable_at segs mem a <-> writable_at segs mem' a)) /\
  (forall a, in_globals G a -> writable_at segs mem a <-> writable_at segs mem' a) /\
  (forall q k i, In (q, k) (user_blocks A) -> ~ In (ptr_addr L q, k) T -> ptr_addr L q <> p -> 0 <= i < k ->
     mbyte segs mem' (ptr_addr L q + i) = mbyte segs mem (ptr_addr L q + i)) /\
  (forall a, lib_scratch B stk regs a -> writable_at segs mem' a) /\
  ll_ret l = 0 /\ ll_out l = [] /\ Fs.fs_sorted (ll_fs l) = true /\
  sink_none B mem' md' /\
  ro_agree segs mem' /\
  res_ok_pack A' (PB (pb_live (TDP T T' b)) (pb_bytes (TDP T T' b)) cs) /\
  (forall i, 0 <= i < n -> mbyte segs mem' (p + i) = mbyte segs mem (p + i)) /\
  tb_live L' A' T' /\
  (forall t, In t T' -> In t (blocks L A) -> In t T).

Definition lib_contract_p (CS : list byte -> list Z) (G R : list (Z * Z))
    (GI : nat -> list (Z * Z) -> (word -> option byte) -> Prop) (j : nat)
    (pc ra empty stk : Z) : Prop :=
  forall L A regs mem md p n pl b T (K : lleaf -> TSet),
    lib_pre_w B API stk empty L A regs mem md ra p n pl ->
    res_ok_pack A b ->
    pack_entry CS pl T b ->
    GI j T mem ->
    tb_live L A T ->
    (0 < n -> ~ In (p, n) T) ->
    G_img_c B R mem ->
    ro_agree segs mem ->
    spZ regs <= TASK_SIZE ->
    frm_zero fp_csr ->
    (forall (l : lleaf) (c' : config),
       (exists (fx' : FPState) L' A' regs' mem' md' T',
          c' = mkCfg (@mkst fx' regs' (Z_to_bv 64 ra) mem' (seg_rom segs)) md' /\
          frm_zero (@fp_csr fx') /\
          lib_post_p (CS pl) G stk L A regs mem md p n b l T T' L' A' regs' mem' md' /\
          GI (S j) T' mem') ->
       realizes segs c' (K l)) ->
    realizes segs (mkCfg (mkst regs (Z_to_bv 64 pc) mem (seg_rom segs)) md) (LIBK pl (m_fs md) K).

Definition lib_post_pg (cs : list Z) (G : list (Z * Z)) (stk : Z) (L : layout) (A : astate) (regs : bvmap 5 word)
    (mem : word -> option byte) (md : Model) (p n : Z) (b : pbound) (l : lleaf)
    (L' : layout) (A' : astate) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) : Prop :=
  MR L' A' mem' md' /\ WF A' /\ bounded A' /\ st_init_done A' = true /\
  getr regs' 10 = Z_to_bv 64 0 /\
  regs_preserved regs regs' /\
  (exists vm' fds' pins', md' = os_upd vm' fds' (ll_fs l) pins' md /\ forall k, fd_lookup fds' k = fd_lookup (m_fds md) k) /\
  (forall q k, In (q, k) (user_blocks A) -> exists q', In (q', k) (user_blocks A') /\ ptr_addr L' q' = ptr_addr L q) /\
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ lib_scratch B stk regs a ->
     mbyte segs mem' a = mbyte segs mem a /\ (writable_at segs mem a <-> writable_at segs mem' a)) /\
  (forall a, in_img B a -> ~ static_owned B a -> ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) ->
     ~ (errno_addr B <= a < errno_addr B + 4) -> ~ in_globals G a ->
     mbyte segs mem' a = mbyte segs mem a /\ (writable_at segs mem a <-> writable_at segs mem' a)) /\
  (forall a, in_globals G a -> writable_at segs mem a <-> writable_at segs mem' a) /\
  (forall q k i, In (q, k) (user_blocks A) -> ptr_addr L q <> p -> 0 <= i < k ->
     mbyte segs mem' (ptr_addr L q + i) = mbyte segs mem (ptr_addr L q + i)) /\
  (forall a, lib_scratch B stk regs a -> writable_at segs mem' a) /\
  ll_ret l = 0 /\ ll_out l = [] /\ Fs.fs_sorted (ll_fs l) = true /\
  sink_none B mem' md' /\
  ro_agree segs mem' /\
  res_ok_pack A' (PB (pb_live b) (pb_bytes b) cs) /\
  (forall i, 0 <= i < n -> mbyte segs mem' (p + i) = mbyte segs mem (p + i)).

Definition lib_contract_pg (CS : list byte -> list Z) (G R : list (Z * Z)) (GI : nat -> (word -> option byte) -> Prop) (j : nat)
    (pc ra empty stk : Z) : Prop :=
  forall L A regs mem md p n pl b (K : lleaf -> TSet),
    lib_pre_w B API stk empty L A regs mem md ra p n pl ->
    res_ok_pack A b ->
    pack_entry CS pl [] b ->
    GI j mem ->
    G_img_c B R mem ->
    ro_agree segs mem ->
    spZ regs <= TASK_SIZE ->
    frm_zero fp_csr ->
    (forall (l : lleaf) (c' : config),
       (exists (fx' : FPState) L' A' regs' mem' md',
          c' = mkCfg (@mkst fx' regs' (Z_to_bv 64 ra) mem' (seg_rom segs)) md' /\
          frm_zero (@fp_csr fx') /\
          lib_post_pg (CS pl) G stk L A regs mem md p n b l L' A' regs' mem' md' /\
          GI (S j) mem') ->
       realizes segs c' (K l)) ->
    realizes segs (mkCfg (mkst regs (Z_to_bv 64 pc) mem (seg_rom segs)) md) (LIBK pl (m_fs md) K).

Lemma lib_post_p_of_pg : forall cs G stk L A regs mem md p n b l L' A' regs' mem' md',
  lib_post_pg cs G stk L A regs mem md p n b l L' A' regs' mem' md' ->
  lib_post_p cs G stk L A regs mem md p n b l [] [] L' A' regs' mem' md'.
Proof using.
  intros cs G stk L A regs mem md p n b l L' A' regs' mem' md'
    (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 & H19 & H20).
  repeat (split; [assumption|]).
  split; [intros q k Hq _; exact (H8 q k Hq)|].
  repeat (split; [assumption|]).
  split; [intros q k i Hq _; exact (H12 q k i Hq)|].
  repeat (split; [assumption|]).
  split; [split; [constructor | intros t Ht; destruct Ht]|].
  intros t Ht. destruct Ht.
Qed.

Lemma lib_contract_p_of_pg : forall CS G R GI j pc ra empty stk,
  lib_contract_pg CS G R GI j pc ra empty stk ->
  lib_contract_p CS G R (fun j T m => T = [] /\ GI j m) j pc ra empty stk.
Proof using.
  intros CS G R GI j pc ra empty stk H L A regs mem md p n pl b T K Hpre Hb He [HT HGI] _ _ HR Hro Hsp Hfrm HK.
  subst T.
  apply (H L A regs mem md p n pl b K Hpre Hb He HGI HR Hro Hsp Hfrm).
  intros l c' (fx' & L' & A' & regs' & mem' & md' & Hc & Hf & Hp & HGI').
  apply HK. exists fx', L', A', regs', mem', md', []. split; [exact Hc|]. split; [exact Hf|].
  split; [exact (lib_post_p_of_pg (CS pl) G stk L A regs mem md p n b l L' A' regs' mem' md' Hp) | split; [reflexivity | exact HGI']].
Qed.
End Pack.
