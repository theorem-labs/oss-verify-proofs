(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import
  PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SRealizes ShapeUpto RefMemcpyLib.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Export AllocCeil.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_LibIface () := "C46Stdlib5Lists4List2hdC47Corelib5Lists7ListDef3mapC47Corelib4Init9Datatypes3fstC35stdpp4base6ElemOfI35stdpp4base<list_elem_of00I35stdpp4base5NoDup00c49OSSVerify5KrLib8LibIface8frame_eqC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3notK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C45stdpp9bitvector;definitions;bv_unsignedc49OSSVerify5KrLib8LibIface7same_onC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00c49OSSVerify5KrLib8LibIface3memC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03".
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition in_ranges (rs : list (Z * Z)) (a : Z) : Prop :=
  exists lo hi, In (lo, hi) rs /\ lo <= a < hi.

Record Layout : Type := LAYOUT {
  ly_malloc      : Z;
  ly_free        : Z;
  ly_new         : Z;
  ly_new_arr     : Z;
  ly_delete      : Z;
  ly_delete_arr  : Z;
  ly_new_handler : Z;
  ly_oom_spin    : Z;
  ly_gp          : Z;
  ly_tp          : Z;
  ly_errno_off   : Z;
  ly_img         : list (Z * Z);
  ly_rw          : list (Z * Z);
  ly_relro       : list (Z * Z);

  ly_rw_img      : forall a, in_ranges ly_rw a -> in_ranges ly_img a;
  ly_errno_rw    : forall a, ly_tp + ly_errno_off <= a < ly_tp + ly_errno_off + 4 -> in_ranges ly_rw a
}.

Definition mem := word -> option byte.

Record mstd {AC : AllocCeiling} (model : Model) : Prop := MSTD {
  ms_halt : m_halted model = None;
  ms_lazy : m_vm_lazy model = [];
  ms_mat  : m_vm_materialized model = [];
  ms_ceil : alloc_top (m_vmmaps model) = alloc_ceiling
}.

Notation kept := keeps_cs.

Definition stack_room (segs : list Segment) (M : mem) (sp : Z) (S : Z) : Prop :=
  RiscvSemantics.store_ok segs M (Z_to_bv 64 (sp - S)) (Z.to_nat S) = true.

Definition frame_eq (F : Z -> Prop) (M M' : mem) : Prop :=
  forall a : word, ~ F (bv_unsigned a) -> M' a = M a.
Definition defined_kept (U : Z -> Prop) (M M' : mem) : Prop :=
  forall a : word, ~ U (bv_unsigned a) -> M a <> None -> M' a <> None.
Definition same_on (P : Z -> Prop) (M M' : mem) : Prop :=
  forall a : word, P (bv_unsigned a) -> M' a = M a.
Lemma frame_eq_same_on : forall F P M M',
  frame_eq F M M' -> (forall a, P a -> ~ F a) -> same_on P M M'.
Proof.
ltac2:(KReplay.run1 (kr_t_LibIface ()) [] "h01ah11Fh22HFh32HPh42Hah51Mh62M'h71Ph81xp;3p;1p;2p-1R0p10000p4p710p8P0p1000GR1p4p710p8P0P1p4p7210p8P0p1000cR1p4p710p8P0P1p4p7210p8P0p1001@R1p4p710R2p8P0P1p4p7210R1p8P0p1001Tp4p710R0p8p10020p4p710R3P2p8P3P1p8P3P0p8g002Ej36Tg003;j15Tg003Tj10Tg0049j12Tg004Wj14Tg005:j21Tg005dj33Tg006YR0p-0R3[P3^80g0077R3f3R1f1R2f0R436f4R5P4O1f6P2O1#5[^00g007h#0#0#0#0#0#0#2R0#4f51104O1P1P2f2R61102P4O2O2W4W0A3516eW3W2X63W5W7W1o"). Qed.

Definition zwin (lo hi : Z) (a : Z) : Prop := lo <= a < hi.

Section Iface.
Context {AC : AllocCeiling}.
Variable SEGS : list Segment.
Variable L : Layout.

#[local] Notation cfg fx R pc M model :=
  (mkCfg (@mkst fx R (Z_to_bv 64 pc) M (seg_rom SEGS)) model).

Record call_regs (R : bvmap 5 word) (sp ret : Z) : Prop := CALL_REGS {
  cr_ra  : getr R 1%bv = Z_to_bv 64 ret;
  cr_ret : ret_ok (Z_to_bv 64 ret);
  cr_ret_range : 0 <= ret < 2 ^ 64;
  cr_sp  : getr R 2%bv = Z_to_bv 64 sp;
  cr_sp16 : sp mod 16 = 0;
  cr_sp_hi : sp < 2 ^ 47;
  cr_gp  : getr R 3%bv = Z_to_bv 64 (ly_gp L);
  cr_tp  : getr R 4%bv = Z_to_bv 64 (ly_tp L)
}.

Definition live_add (p n : Z) (lv lv' : list (Z * Z)) : Prop := lv' = (p, n) :: lv /\ ~ In p (map fst lv).
Definition live_del (p : Z) (lv lv' : list (Z * Z)) : Prop := forall q k, In (q, k) lv' <-> (In (q, k) lv /\ q <> p).

Fixpoint count_class_f (cls : Z -> Z) (big : Z) (lv : list (Z * Z)) (c : Z) : Z :=
  match lv with
  | [] => 0
  | (_, n) :: lv' => (if (n <? big) && (cls n =? c) then 1 else 0) + count_class_f cls big lv' c
  end.
Fixpoint big_bytes_f (rb : Z -> Z) (big : Z) (lv : list (Z * Z)) : Z :=
  match lv with
  | [] => 0
  | (_, n) :: lv' => (if big <=? n then rb n else 0) + big_bytes_f rb big lv'
  end.

Definition errno_win (a : Z) : Prop := zwin (ly_tp L + ly_errno_off L) (ly_tp L + ly_errno_off L + 4) a.

Definition img_ro_clear (M : mem) : Prop :=
  forall w : word, in_ranges (ly_img L) (bv_unsigned w) -> ~ in_ranges (ly_rw L) (bv_unsigned w) -> M w = None.

Record MallocIface : Type := MALLOC_IFACE {

  AS    : Type;
  ainv  : AS -> mem -> Model -> Prop;
  live  : AS -> list (Z * Z);
  owned : AS -> Z -> Prop;

  size_class : Z -> Z;
  BIG   : Z;
  NMAX  : Z;
  round_big : Z -> Z;
  caps  : AS -> Z -> Z;
  bigcap : AS -> Z;
  room_for : AS -> Z -> Prop;

  MALLOC_STACK : Z;

  ai_big_pos   : 0 < BIG <= NMAX;
  ai_nmax_bound : NMAX < 2 ^ 40;
  ai_round_big_mono : forall n m, 0 <= n <= m -> round_big n <= round_big m;
  ai_round_big_nonneg : forall n, 0 <= n -> 0 <= round_big n;
  ai_size_class_range : forall n, 0 <= n < BIG -> 0 <= size_class n < 63;

  room_small : forall A M model n, ainv A M model -> 0 <= n < BIG ->
      count_class_f size_class BIG (live A) (size_class n) + 1 <= caps A (size_class n) ->
      count_class_f size_class BIG (live A) (size_class n + 1) + 1 <= caps A (size_class n + 1) ->
      room_for A n;
  room_big : forall A M model n, ainv A M model -> BIG <= n <= NMAX ->
      big_bytes_f round_big BIG (live A) + round_big n <= bigcap A ->
      room_for A n;
  ai_mstd      : forall A M model, ainv A M model -> m_vm_lazy model = [];
  ai_live_block : forall A M model p n, ainv A M model -> In (p, n) (live A) ->
      0 <= n /\ p mod 16 = 0 /\ 0 < p /\ p + n <= alloc_ceiling
      /\ (forall a, p <= a < p + n -> ~ owned A a /\ ~ in_ranges (ly_img L) a /\ M (Z_to_bv 64 a) <> None);
  ai_live_nodup : forall A M model, ainv A M model -> NoDup (map fst (live A));
  ai_live_disjoint : forall A M model p n q k, ainv A M model ->
      In (p, n) (live A) -> In (q, k) (live A) -> p <> q -> p + n <= q \/ q + k <= p;
  ai_owned_not_img_ro : forall A M model a, ainv A M model -> owned A a ->
      in_ranges (ly_rw L) a \/ ~ in_ranges (ly_img L) a;
  ai_owned_below_ceiling : forall A M model a, ainv A M model -> owned A a -> ~ in_ranges (ly_img L) a ->
      0 < a < alloc_ceiling;

  static_cells : list (Z * list Z);
  ai_static_cells : forall A M model a bs, ainv A M model -> In (a, bs) static_cells ->
      rdn SEGS M (Z_to_bv 64 a) (length bs) = Some (map (Z_to_bv 8) bs);
  ai_static_cells_owned : forall A M model a bs i, ainv A M model -> In (a, bs) static_cells ->
      0 <= i < Z.of_nat (length bs) -> owned A (a + i);

  ai_frame : forall A M M' model model', ainv A M model ->
      (forall a : word, owned A (bv_unsigned a) -> M' a = M a) ->
      (forall a : word, M a <> None -> M' a <> None) ->
      m_vmmaps model' = m_vmmaps model -> m_vm_lazy model' = m_vm_lazy model ->
      ainv A M' model';

  may_fail : AS -> Z -> Prop;
  may_fail_big : forall A n, BIG <= n -> may_fail A n;

  mi_malloc : forall (fx : FPState) A R M model (n sp ret : Z) (Ksucc : TSet),

      ainv A M model -> mstd model -> img_ro_clear M ->
      call_regs R sp ret -> getr R 10%bv = Z_to_bv 64 n -> 0 <= n <= NMAX ->
      alloc_ceiling + MALLOC_STACK <= sp ->
      stack_room SEGS M sp MALLOC_STACK ->
      (forall a, zwin (sp - MALLOC_STACK) sp a -> ~ owned A a) ->
      room_for A n ->

      (forall A' R' M' model' (p : Z),
          ainv A' M' model' -> mstd model' -> m_fs model' = m_fs model -> m_fds model' = m_fds model ->
          kept R R' -> getr R' 10%bv = Z_to_bv 64 p -> 0 < p ->
          live_add p n (live A) (live A') -> caps A' = caps A -> bigcap A' = bigcap A ->
          (forall a, owned A' a -> owned A a \/ (~ in_ranges (ly_img L) a /\ M (Z_to_bv 64 a) = None)) ->
          frame_eq (fun a => owned A' a \/ (p <= a < p + n) \/ zwin (sp - MALLOC_STACK) sp a \/ errno_win a) M M' ->
          (forall a : word, M a <> None -> M' a <> None \/ owned A (bv_unsigned a) \/ errno_win (bv_unsigned a)) ->
          srealizes SEGS (cfg fx R' ret M' model') Ksucc) ->
      srealizes SEGS (cfg fx R (ly_malloc L) M model) Ksucc;

  mi_free : forall (fx : FPState) A R M model (p n sp ret : Z) (K : TSet),
      ainv A M model -> mstd model -> img_ro_clear M ->
      call_regs R sp ret -> getr R 10%bv = Z_to_bv 64 p ->
      (p = 0 /\ n = 0 \/ In (p, n) (live A)) ->
      alloc_ceiling + MALLOC_STACK <= sp ->
      stack_room SEGS M sp MALLOC_STACK ->
      (forall a, zwin (sp - MALLOC_STACK) sp a -> ~ owned A a) ->
      (forall A' R' M' model',
          ainv A' M' model' -> mstd model' -> m_fs model' = m_fs model -> m_fds model' = m_fds model ->
          kept R R' ->
          live_del p (live A) (live A') -> caps A' = caps A -> bigcap A' = bigcap A ->
          (forall a, owned A' a -> owned A a \/ (p <= a < p + n)) ->
          frame_eq (fun a => owned A a \/ (p <= a < p + n) \/ zwin (sp - MALLOC_STACK) sp a \/ errno_win a) M M' ->
          (forall a : word, M a <> None -> M' a <> None \/ owned A (bv_unsigned a) \/ (p <= bv_unsigned a < p + n) \/ errno_win (bv_unsigned a)) ->
          srealizes SEGS (cfg fx R' ret M' model') K) ->
      srealizes SEGS (cfg fx R (ly_free L) M model) K
}.

Record StaticsIface : Type := STATICS_IFACE {
  SX : Type;
  sx_le : SX -> SX -> Prop;
  sx_inv : SX -> mem -> Prop;
  sx_region : Z -> Prop;
  sx_le_refl : forall s, sx_le s s;
  sx_le_trans : forall a b c, sx_le a b -> sx_le b c -> sx_le a c;
  sx_region_rw : forall a, sx_region a -> in_ranges (ly_rw L) a;

  sx_frame : forall s M M', sx_inv s M ->
      same_on (fun a => sx_region a \/ in_ranges (ly_relro L) a) M M' -> sx_inv s M';

  sx_relro : forall s M a, sx_inv s M -> in_ranges (ly_relro L) a -> M (Z_to_bv 64 a) = None;

  sx_handler_set : SX -> Prop;
  sx_handler_mono : forall s s', sx_le s s' -> sx_handler_set s -> sx_handler_set s';
  sx_handler_cell : forall s M, sx_inv s M -> sx_handler_set s ->
      rdn SEGS M (Z_to_bv 64 (ly_new_handler L)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (ly_oom_spin L)))
}.

Section Derived.
Variable MI : MallocIface.
Variable ST : StaticsIface.

Definition count_class (A : AS MI) (c : Z) : Z := count_class_f (size_class MI) (BIG MI) (live MI A) c.
Definition big_bytes (A : AS MI) : Z := big_bytes_f (round_big MI) (BIG MI) (live MI A).

Definition new_size (n : Z) : Z := Z.max n 1.

Definition new_rule_stmt (NEW_STACK : Z) : Prop :=
  forall (fx : FPState) A (s : SX ST) R M model (n sp ret : Z) (K : TSet),
    ainv MI A M model -> mstd model -> img_ro_clear M -> sx_inv ST s M -> sx_handler_set ST s ->
    call_regs R sp ret -> getr R 10%bv = Z_to_bv 64 n -> 0 <= n <= NMAX MI ->
    alloc_ceiling + NEW_STACK <= sp ->
    stack_room SEGS M sp NEW_STACK ->
    (forall a, zwin (sp - NEW_STACK) sp a -> ~ owned MI A a /\ ~ sx_region ST a) ->
    (forall a, owned MI A a -> ~ sx_region ST a) -> (forall a, errno_win a -> ~ sx_region ST a) ->
    room_for MI A (new_size n) ->
    (forall A' R' M' model' (p : Z),
        ainv MI A' M' model' -> mstd model' -> m_fs model' = m_fs model -> m_fds model' = m_fds model ->
        sx_inv ST s M' ->
        kept R R' -> getr R' 10%bv = Z_to_bv 64 p -> 0 < p ->
        live_add p (new_size n) (live MI A) (live MI A') -> caps MI A' = caps MI A -> bigcap MI A' = bigcap MI A ->
        (forall a, owned MI A' a -> owned MI A a \/ (~ in_ranges (ly_img L) a /\ M (Z_to_bv 64 a) = None)) ->
        frame_eq (fun a => owned MI A' a \/ (p <= a < p + new_size n) \/ zwin (sp - NEW_STACK) sp a \/ errno_win a) M M' ->
        (forall a : word, M a <> None -> M' a <> None \/ owned MI A (bv_unsigned a) \/ errno_win (bv_unsigned a)) ->
        srealizes SEGS (cfg fx R' ret M' model') K) ->
    srealizes SEGS (cfg fx R (ly_new L) M model) K.

Definition delete_rule_stmt (DEL_STACK : Z) : Prop :=
  forall (fx : FPState) A R M model (p n sp ret : Z) (K : TSet),
    ainv MI A M model -> mstd model -> img_ro_clear M ->
    call_regs R sp ret -> getr R 10%bv = Z_to_bv 64 p ->
    (p = 0 /\ n = 0 \/ In (p, n) (live MI A)) ->
    alloc_ceiling + DEL_STACK <= sp ->
    stack_room SEGS M sp DEL_STACK ->
    (forall a, zwin (sp - DEL_STACK) sp a -> ~ owned MI A a) ->
    (forall A' R' M' model',
        ainv MI A' M' model' -> mstd model' -> m_fs model' = m_fs model -> m_fds model' = m_fds model ->
        kept R R' ->
        live_del p (live MI A) (live MI A') -> caps MI A' = caps MI A -> bigcap MI A' = bigcap MI A ->
        (forall a, owned MI A' a -> owned MI A a \/ (p <= a < p + n)) ->
        frame_eq (fun a => owned MI A a \/ (p <= a < p + n) \/ zwin (sp - DEL_STACK) sp a \/ errno_win a) M M' ->
        (forall a : word, M a <> None -> M' a <> None \/ owned MI A (bv_unsigned a) \/ (p <= bv_unsigned a < p + n) \/ errno_win (bv_unsigned a)) ->
        srealizes SEGS (cfg fx R' ret M' model') K) ->
    srealizes SEGS (cfg fx R (ly_delete L) M model) K.

End Derived.
End Iface.

Arguments AS {AC SEGS L} _.
Arguments ainv {AC SEGS L} _ _ _ _.
Arguments live {AC SEGS L} _ _.
Arguments owned {AC SEGS L} _ _ _.
Arguments caps {AC SEGS L} _ _ _.
Arguments bigcap {AC SEGS L} _ _.
Arguments room_for {AC SEGS L} _ _ _.
Arguments may_fail {AC SEGS L} _ _ _.
Arguments size_class {AC SEGS L} _ _.
Arguments BIG {AC SEGS L} _.
Arguments NMAX {AC SEGS L} _.
Arguments round_big {AC SEGS L} _ _.
Arguments MALLOC_STACK {AC SEGS L} _.
Arguments mi_malloc {AC SEGS L} _.
Arguments mi_free {AC SEGS L} _.
Arguments may_fail_big {AC SEGS L} _.
Arguments room_small {AC SEGS L} _.
Arguments room_big {AC SEGS L} _.
Arguments ai_frame {AC SEGS L} _.
Arguments static_cells {AC SEGS L} _.
Arguments ai_static_cells {AC SEGS L} _.
Arguments ai_static_cells_owned {AC SEGS L} _.

Arguments ai_round_big_nonneg {AC SEGS L} _.
Arguments ai_round_big_mono {AC SEGS L} _.
Arguments ai_size_class_range {AC SEGS L} _.
Arguments ai_live_block {AC SEGS L} _.
Arguments ai_live_disjoint {AC SEGS L} _.
Arguments ai_live_nodup {AC SEGS L} _.
Arguments ai_owned_not_img_ro {AC SEGS L} _.
Arguments ai_owned_below_ceiling {AC SEGS L} _.
Arguments ai_mstd {AC SEGS L} _.
Arguments ai_big_pos {AC SEGS L} _.
Arguments ai_nmax_bound {AC SEGS L} _.
Arguments sx_frame {SEGS L} _.
Arguments sx_relro {SEGS L} _.
Arguments sx_handler_cell {SEGS L} _.
Arguments sx_handler_mono {SEGS L} _.
Arguments sx_region_rw {SEGS L} _.
Arguments SX {SEGS L} _.
Arguments sx_inv {SEGS L} _ _ _.
Arguments sx_le {SEGS L} _ _ _.
Arguments sx_region {SEGS L} _ _.
Arguments sx_handler_set {SEGS L} _ _.

Section Compat.
Context {AC : AllocCeiling}.
Variable SEGS : list Segment.
Variable L : Layout.
Variable MI : MallocIface SEGS L.

End Compat.
