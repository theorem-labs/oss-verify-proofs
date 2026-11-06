From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib Require Import Contract AllocSlots AllocRoom.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Import Mem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import WriterSpec WriterApp Ledger.
Import ListNotations.
Local Open Scope Z_scope.

Definition PUT : Z := 0x16278.
Definition PUT_K : Z := 48 + (REALLOC_STACK + 48).
Definition WMAX : Z := 2 ^ 28.

Definition wbc (b : sbound) (c : Z) : sbound := if c =? 0 then b else sb_malloc b (c + 16).

Definition wr_room (b : sbound) : Prop :=
  sb_live b + 2 <= sb_cap b <= CAPMAX /\ 0 <= sb_bytes b /\ sb_bytes b + 2 ^ 29 + 32 <= 2 ^ 40.

Definition fast_writes (o buf len n a : Z) : Prop :=
  o + 8 <= a < o + 16 \/ buf + len <= a < buf + len + n + 1.

Definition null_writes (o buf cap a : Z) : Prop :=
  o + 24 <= a < o + 28 \/ alloc_statics a \/ (cap <> 0 /\ buf - 16 <= a < buf + cap).

Definition grow_writes (o buf cap q c a : Z) : Prop :=
  o <= a < o + 24 \/ alloc_statics a \/ (cap <> 0 /\ buf - 16 <= a < buf + cap) \/ q - 16 <= a < q + c.

Definition wstep (F : ResForm) (b : rf_R F) (c c' : Z) : rf_R F :=
  if c =? 0 then rf_malloc F b (c' + 16) else rf_realloc F b (c + 16) (c' + 16).

Section K.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Variable F : ResForm.
Let segs := ms_segs B.
Let MR := aa_MR API.

Definition word4_mem (mem : word -> option byte) (a v : Z) : Prop :=
  forall k, (k < 4)%nat -> mbyte segs mem (a + Z.of_nat k) = Some (Z_to_bv 8 (le_byte v 4 k)).

Definition zbytes_at (mem : word -> option byte) (a : Z) (l : list Z) : Prop :=
  forall i, 0 <= i < Z.of_nat (length l) -> mbyte segs mem (a + i) = Some (Z_to_bv 8 (nth (Z.to_nat i) l 0)).

Definition off_errno (a n : Z) : Prop := a + n <= errno_addr B \/ errno_addr B + 4 <= a.

Definition pj_out_ok (mem : word -> option byte) (Lam : list (Z * Z))
    (o buf len cap failed : Z) (text : list Z) : Prop :=
  o mod 8 = 0 /\ 0 <= o /\ o + 32 <= 2 ^ 64 /\
  (forall i, 0 <= i < 32 -> writable_at segs mem (o + i) /\ exists v, mbyte segs mem (o + i) = Some v) /\
  0 <= buf < 2 ^ 64 /\ 0 <= len < 2 ^ 64 /\ 0 <= cap < 2 ^ 64 /\
  word_mem segs mem o buf /\ word_mem segs mem (o + 8) len /\ word_mem segs mem (o + 16) cap /\
  word4_mem mem (o + 24) failed /\ (failed = 0 \/ failed = 1) /\
  bytes_ok text /\ Z.of_nat (length text) = len /\
  ((cap = 0 /\ buf = 0 /\ len = 0) \/
   ((exists j, 0 <= j <= 51 /\ cap = 4096 * 2 ^ j) /\ In (buf, cap) Lam /\
    (forall i, 0 <= i < cap + 16 -> ~ alloc_statics (buf - 16 + i)) /\
    len < cap /\ zbytes_at mem buf (text ++ [0]))).

Definition s_where (regs : bvmap 5 word) (Lam : list (Z * Z)) (s n buf : Z) : Prop :=
  (spZ regs <= s /\ off_errno s n) \/
  (in_img B s /\ forall i, 0 <= i < n -> ro_addr rsegs (wa (s + i)) = true) \/
  (exists x y, In (x, y) Lam /\ x <> buf /\ x <= s /\ s + n <= x + y).

Definition call_post_e (stk : Z) (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte)
    (md : Model) (E : Z -> Prop) (gone : Z)
    (L' : layout) (A' : astate) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) : Prop :=
  MR L' A' mem' md' /\ WF A' /\ bounded A' /\ layout_le A L L' /\
  (forall p n, In (p, n) (user_blocks A) -> ptr_addr L p <> gone ->
     In (p, n) (user_blocks A') /\ ptr_addr L' p = ptr_addr L p) /\
  regs_preserved regs regs' /\
  (exists vm', md' = with_vmmaps vm' md) /\
  (forall a, (alloc_ceiling <= a < 2 ^ 64 \/ in_img B a) ->
     ~ owned B L A a -> ~ owned B L' A' a -> ~ scratch_k B stk regs a -> ~ E a ->
     mbyte segs mem' a = mbyte segs mem a /\ (writable_at segs mem a <-> writable_at segs mem' a)) /\
  (forall p n i, In (p, n) (user_blocks A) -> In (p, n) (user_blocks A') -> 0 <= i < n ->
     ~ E (ptr_addr L p + i) ->
     mbyte segs mem' (ptr_addr L p + i) = mbyte segs mem (ptr_addr L p + i)) /\
  (forall a, scratch_k B stk regs a -> writable_at segs mem' a).

Definition put_ret (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
    (o n buf len cap failed : Z) (text bs : list Z) (Lam : list (Z * Z)) (peak cnt fail : Z) (calls : list Z)
    (b : rf_R F) (c' : config) : Prop :=
  let st' := put1 (mkW failed text cap cnt fail calls) bs in
  let c1 := newcap cap (len + n + 1) in
  exists L' A' regs' mem' md' buf' Lam' peak' b',
    c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom segs)) md' /\
    ro_agree segs mem' /\ guard_kept B mem mem' /\
    (st_init_done A = true -> st_init_done A' = true) /\
    (length (st_regions A) <= length (st_regions A'))%nat /\
    pj_out_ok mem' Lam' o buf' (Z.of_nat (length (w_text st'))) (w_cap st') (w_failed st') (w_text st') /\
    ledger B L' A' mem' Lam' peak' (w_cnt st') (w_fail st') /\
    rf_ok F A' b' /\
    ( (failed <> 0 /\ L' = L /\ A' = A /\ md' = md /\ buf' = buf /\ Lam' = Lam /\ peak' = peak /\ b' = b /\
       keeps B L A mem mem' 0 /\ ublocks_kept L A A' (0, 0) /\
       call_post_e PUT_K L A regs mem md (fun _ => False) 0 L A regs' mem' md)
    \/ (failed = 0 /\ len + n + 1 <= cap /\ L' = L /\ A' = A /\ md' = md /\ buf' = buf /\ Lam' = Lam /\
       peak' = peak /\ b' = b /\ keeps B L A mem mem' (buf - 16) /\ ublocks_kept L A A' (0, 0) /\
       call_post_e PUT_K L A regs mem md (fast_writes o buf len n) 0 L A regs' mem' md)
    \/ (failed = 0 /\ cap < len + n + 1 /\ cnt = fail /\ buf' = buf /\ Lam' = Lam /\ peak' = peak /\
       b' = b /\ blocks L' A' = blocks L A /\ keeps B L A mem mem' 0 /\ ublocks_kept L A A' (0, 0) /\
       call_post_e PUT_K L A regs mem md (null_writes o buf cap) 0 L' A' regs' mem' md')
    \/ (failed = 0 /\ cap < len + n + 1 /\ cnt <> fail /\ buf' <> 0 /\
       b' = wstep F b cap c1 /\
       keeps B L A mem mem' (buf - 16) /\ ublocks_kept L A A' (buf - 16, cap + 16) /\
       call_post_e PUT_K L A regs mem md (grow_writes o buf cap buf' c1) (buf - 16) L' A' regs' mem' md' /\
       (exists c1' c2', blocks L' A' = c1' ++ (buf' - 16, c1 + 16) :: c2' /\
          (cap = 0 /\ c1' ++ c2' = blocks L A \/
           cap <> 0 /\ exists b1 b2, blocks L A = b1 ++ (buf - 16, cap + 16) :: b2 /\ c1' ++ c2' = b1 ++ b2)) /\
       exists l1 l2, (cap = 0 /\ l1 = [] /\ l2 = Lam \/ cap <> 0 /\ Lam = l1 ++ (buf, cap) :: l2) /\
         Lam' = (buf', c1) :: l1 ++ l2 /\ peak' = Z.max peak (lsum (l1 ++ l2) + c1)) ).

Definition put_contract : Prop :=
  forall L A regs mem md b o s n buf len cap failed (text bs : list Z) Lam peak cnt fail calls,
    segs = rsegs ->
    call_pre_k B MR PUT_K L A regs mem md ->
    ro_agree segs mem ->
    getr regs 10 = Z_to_bv 64 o -> getr regs 11 = Z_to_bv 64 s -> getr regs 12 = Z_to_bv 64 n ->
    pj_out_ok mem Lam o buf len cap failed text ->
    ledger B L A mem Lam peak cnt fail ->
    spZ regs <= o -> off_errno o 32 -> off_errno (spZ regs - PUT_K) PUT_K ->
    zbytes_at mem s bs -> Z.of_nat (length bs) = n -> bytes_ok bs -> 0 <= s < 2 ^ 64 -> s + n <= 2 ^ 64 ->
    s_where regs Lam s n buf -> (s + n <= o \/ o + 32 <= s) ->
    len + n + 1 <= WMAX ->
    rf_ok F A b -> (failed = 0 -> cap < len + n + 1 -> rf_room F b (newcap cap (len + n + 1) + 16)) ->
    SR segs (mkCfg (mkst regs (Z_to_bv 64 PUT) mem (seg_rom segs)) md)
      (put_ret L A regs mem md o n buf len cap failed text bs Lam peak cnt fail calls b).

End K.
