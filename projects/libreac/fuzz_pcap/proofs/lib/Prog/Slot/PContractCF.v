From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SymAddr.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK11 YK0i YK0o YK0s YK15 YM06 YP09 YO05.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YO0i YO0f YO0d YO0p YO0j YO0m YO0l YO0n YO0k
  YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import Contract OutForm Img0 SlotAgree.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Lib Require Import Mem Cells Step Frame FP Arr.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog Require Import StdioModel fmemopen_c fclose_c libreac_fuzz_fopen_c
  pcap_source_struct pcap_source_struct_next pcap_source_open_c pcap_source_close_c pcap_source_next_c.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog.Slot Require Import PSROcf.
Import ListNotations.
Local Open Scope Z_scope.

(* The cut-free twins of the three reader contracts of the fuzz_pcap ubsan slot: each is its contract of
   lib/U/Prog/pcap_source_*_c.v with SR replaced by SRcf (SlotAgree.v) and SRO by SROcf (PSROcf.v): the same
   premises and posts, and no configuration the call can reach is refused by the memory budget. The open contract's
   room for the stream's 1304-byte block is room_cf (the cut-free malloc's room), not room_slots. *)

Section KO.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let segs := ms_segs B.
Let MR := aa_MR API.

Definition pcap_source_open_contract_cf : Prop :=
  forall L A regs mem md (ps pth b : Z) (Fc : list byte) (f sw olen vtag vid : word) (pad : list byte)
         (b0 : sbound),
    segs = rsegs ->
    call_pre_k B MR OPEN_K L A regs mem md ->
    getr regs 10 = Z_to_bv 64 ps -> ps <> 0 -> ps mod 8 = 0 -> spZ regs <= ps ->
    rw_cells rsegs mem ps (ps_cells f sw olen vtag vid pad) ->
    getr regs 11 = Z_to_bv 64 pth -> pth <> 0 -> bytes_at rsegs mem pth (PATH_STR ++ [Z_to_bv 8 0]) ->
    (pth + 13 <= spZ regs - OPEN_K \/ spZ regs <= pth) ->
    bytes_at rsegs mem G_FILE_LEN (le8 (wz (Z.of_nat (length Fc))) ++ le8 (wz b)) ->
    Z.of_nat (length Fc) < 2 ^ 26 ->
    ((1 <= length Fc)%nat -> In (b, Z.of_nat (length Fc)) (blocks L A) /\ bytes_at rsegs mem b Fc) ->
    stdio_ok mem -> ofl_empty mem -> guard_ok mem -> ro_agree segs mem ->
    res_ok_slots A b0 -> room_cf md b0 1304 ->
    SRcf B (mkCfg (mkst regs (Z_to_bv 64 PCAP_SOURCE_OPEN) mem (seg_rom segs)) md)
      (fun c' => exists L' A' regs' mem' md' h,
         c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom segs)) md' /\
         call_post_k B MR OPEN_K L A regs mem md (open_writes B ps h) L' A' regs' mem' md' /\
         stdio_ok mem' /\ guard_ok mem' /\ ro_agree segs mem' /\
         (pcap_good Fc = false ->
            getr regs' 10 = Z_to_bv 64 (-1) /\
            rw_cells rsegs mem' ps (ps_cells (wz 0) sw (wz 0) (wz 0) (wz 0) pad) /\
            ofl_empty mem' /\ blocks L' A' = blocks L A /\
            blocks_kept B L A mem mem' (fun _ => False) /\
            (forall q k, In (q, k) (user_blocks A) -> ptr_addr L q <> h -> In (q, k) (user_blocks A')) /\
            (length (st_regions A) <= length (st_regions A'))%nat /\
            (length Fc = 0%nat -> h = 0 /\ L' = L /\ A' = A /\ md' = md /\ res_ok_slots A' b0) /\
            ((1 <= length Fc)%nat ->
               h <> 0 /\ fresh_block B h 1304 /\ st_init_done A' = true /\
               res_ok_slots A' (sb_free (sb_malloc b0 1304) 1304) /\ bytes_at rsegs mem' b Fc)) /\
         (pcap_good Fc = true ->
            getr regs' 10 = Z_to_bv 64 0 /\ h <> 0 /\ h mod 16 = 0 /\ fresh_block B h 1304 /\
            rw_cells rsegs mem' ps (ps_cells (wz h) (wz (pcap_sw Fc)) (wz 0) (wz 0) (wz 0) pad) /\
            (exists b1 b2, blocks L' A' = b1 ++ (h, 1304) :: b2 /\ blocks L A = b1 ++ b2) /\
            blocks_kept B L A mem mem' (fun _ => False) /\
            (forall q k, In (q, k) (user_blocks A) -> In (q, k) (user_blocks A')) /\
            st_init_done A' = true /\ (length (st_regions A) <= length (st_regions A'))%nat /\
            res_ok_slots A' (sb_malloc b0 1304) /\
            mstl mem' h b Fc 24 (wz 0) (wz 0) /\ ofl_one mem' h)).

Definition pcap_source_close_contract_cf : Prop :=
  forall L A regs mem md (ps h : Z) (sw olen vtag vid : word) (pad : list byte) (b p : Z) (Fc : list byte)
         (b0 : sbound),
    segs = rsegs ->
    call_pre_k B MR CLOSE_K L A regs mem md ->
    getr regs 10 = Z_to_bv 64 ps -> ps <> 0 -> ps mod 8 = 0 -> spZ regs <= ps ->
    rw_cells rsegs mem ps (ps_cells (wz h) sw olen vtag vid pad) -> 0 <= h < 2 ^ 64 ->
    (h <> 0 ->
       In (h, 1304) (blocks L A) /\ In (b, Z.of_nat (length Fc)) (blocks L A) /\
       mstl mem h b Fc p (wz 0) (wz 0) /\ ofl_one mem h /\ stdio_ok mem) ->
    guard_ok mem -> ro_agree segs mem -> res_ok_slots A b0 ->
    SRcf B (mkCfg (mkst regs (Z_to_bv 64 PCAP_SOURCE_CLOSE) mem (seg_rom segs)) md)
      (fun c' => exists L' A' regs' mem' md',
         c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom segs)) md' /\
         call_post_k B MR CLOSE_K L A regs mem md (close_writes ps h) L' A' regs' mem' md' /\
         rw_cells rsegs mem' ps (ps_cells (wz 0) sw olen vtag vid pad) /\
         guard_ok mem' /\ ro_agree segs mem' /\
         (h = 0 ->
            L' = L /\ A' = A /\ md' = md /\ Frame.munch [(spZ regs - 16, spZ regs)] mem mem' /\
            res_ok_slots A' b0) /\
         (h <> 0 ->
            (exists b1 b2, blocks L A = b1 ++ (h, 1304) :: b2 /\ blocks L' A' = b1 ++ b2) /\
            blocks_kept B L A mem mem' (fun a => a = h) /\
            (forall q k, In (q, k) (user_blocks A) -> ptr_addr L q <> h -> In (q, k) (user_blocks A')) /\
            (st_init_done A = true -> st_init_done A' = true) /\
            (length (st_regions A) <= length (st_regions A'))%nat /\
            res_ok_slots A' (sb_free b0 1304) /\
            ofl_empty mem' /\ stdio_ok mem' /\ bytes_at rsegs mem' b Fc)).

End KO.

Section KN.
Context {fx : YK11.FPState}.

Definition pcap_source_next_contract_cf : Prop :=
  forall regs mem md (ps buf cap ts h swz b p fl mdv lo : Z) (lol lvt lvid pv nx tsv : word) (pad bj Fc : list byte),
    getr regs 10 = wz ps -> getr regs 11 = wz buf -> getr regs 12 = wz cap -> getr regs 13 = wz ts ->
    YK0s.ret_ok (getr regs 1) ->
    spZ regs <= ps -> rw_cells rsegs mem ps (ps_cells (wz h) (wz swz) lol lvt lvid pad) -> 0 <= h < 2 ^ 64 ->
    (h <> 0 ->
       mstl mem h b Fc p pv nx /\ (swz = 0 \/ swz = 1) /\ Z.of_nat (length Fc) < 2 ^ 26 /\
       h + 1304 <= lo /\ b + Z.of_nat (length Fc) <= lo /\ img_apart h 1304 /\
       (buf + Z.max cap 1 <= h \/ h + 1304 <= buf) /\ (buf + Z.max cap 1 <= b \/ b + Z.of_nat (length Fc) <= buf) /\
       (Fc <> [] -> img_apart b (Z.of_nat (length Fc)))) ->
    0 <= cap < 2 ^ 64 -> 4096 <= buf -> u8arr rsegs mem buf bj -> Z.of_nat (length bj) = Z.max cap 1 ->
    img_apart buf (Z.max cap 1) -> buf + Z.max cap 1 <= lo ->
    (ts <> 0 -> spZ regs <= ts /\ (ts + 8 <= ps \/ ps + 24 <= ts) /\ rw_cells rsegs mem ts [C8 tsv]) ->
    bytes_at rsegs mem A_GOT_STDERR (le8 (wz A_STDERR_VAR)) -> bytes_at rsegs mem A_STDERR_VAR (le8 (wz A_STDERR)) ->
    errf mem fl mdv -> guard_ok mem -> ro_agree rsegs mem ->
    stk rsegs mem lo (spZ regs) -> lo + NEXT_K <= spZ regs -> (symaddr ImgPages.Plain.top) <= lo -> spZ regs <= 2 ^ 47 ->
    frm0 (@YK11.fp_csr fx) -> m_halted md = None -> m_vm_lazy md = [] -> fdchan (wz 2) ch_stderr md ->
    SROcf rsegs (mkCfg (mkst regs (wz PCAP_SOURCE_NEXT) mem (seg_rom rsegs)) md) (psn_out h (swz =? 1) Fc cap p)
      (fun c' => exists regs' mem' (Ft : bvmap 5 word) (fc' : bv 32) (mdv' : Z),
         c' = mkCfg (@YK11.mkst (YK11.mkFP Ft fc') regs' (getr regs 1) mem' (seg_rom rsegs)) md /\
         frm0 fc' /\ (forall k : reg, bv_unsigned k <> 10 -> reg_get Ft k = reg_get (@YK11.fp_regs fx) k) /\
         regs_preserved regs regs' /\
         munch [(spZ regs - NEXT_K, spZ regs); (A_STDERR, A_STDERR + 232); (ps, ps + 24);
                (buf, buf + Z.max cap 1); (ts, ts + (if ts =? 0 then 0 else 8)); (h, h + 1304)] mem mem' /\
         wmono rsegs mem mem' /\ errf mem' fl mdv' /\ guard_ok mem' /\ ro_agree rsegs mem' /\
         stk rsegs mem' lo (spZ regs) /\
         (h = 0 -> getr regs' 10 = wz (-1) /\ munch [(spZ regs - 112, spZ regs)] mem mem') /\
         (h <> 0 -> psn_open_post (swz =? 1) Fc cap p regs' mem' ps buf ts h b swz lol lvt lvid pad pv nx bj tsv)).

End KN.
