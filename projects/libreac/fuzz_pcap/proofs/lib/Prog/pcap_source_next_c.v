From OSSVerify.libreac.fuzz_pcap Require Symbols.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SymAddr.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK11 YK0i YK0o YK0s YK15 YM06 YP09 YO05.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YO0i YO0f YO0d.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import Contract OutForm Img0.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Lib Require Import Mem Cells Step Frame FP Arr.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog Require Import StdioModel pcap_source_struct pcap_source_struct_next.
Import ListNotations.
Local Open Scope Z_scope.

Definition PCAP_SOURCE_NEXT : Z := Eval compute in Symbols.Plain.s_pcap_source_next.
Definition NEXT_K : Z := 5744.
Definition A_GOT_STDERR : Z := Eval compute in (Symbols.Plain.Sec.s_got + 0x40)%Z.
Definition A_STDERR_VAR : Z := Eval compute in Symbols.Plain.s_stderr.

Definition psn_open_post (sw : bool) (Fc : list byte) (cap p : Z) (regs' : bvmap 5 word) (mem' : word -> option byte)
    (ps buf ts h b swz : Z) (lol lvt lvid : word) (pad : list byte) (pv nx : word) (bj : list byte) (tsv : word) : Prop :=
  getr regs' 10 = wz (res_of sw Fc cap (psn_q sw Fc cap p)) /\
  mstl mem' h b Fc (pos_of sw Fc cap (psn_q sw Fc cap p)) pv nx /\
  rw_cells rsegs mem' ps (ps_cells (wz h) (wz swz) (lol_of sw Fc (psn_lh sw Fc cap p) lol)
                            (vt_of sw Fc cap (psn_q sw Fc cap p) lvt) (vid_of sw Fc cap (psn_q sw Fc cap p) lvid) pad) /\
  (exists bj', u8arr rsegs mem' buf bj' /\ length bj' = length bj /\
     (is_fit (kind sw Fc cap (psn_q sw Fc cap p)) = true ->
        firstn (Z.to_nat (incl sw Fc (psn_q sw Fc cap p))) bj' = rec_bytes sw Fc (psn_q sw Fc cap p))) /\
  (ts <> 0 -> rw_cells rsegs mem' ts [C8 (ts_of sw Fc cap (psn_q sw Fc cap p) tsv)]).

Section K.
Context {fx : YK11.FPState}.

Definition pcap_source_next_contract : Prop :=
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
    (* the page-rounded end of the image, the end of .bss rounded up to a page (0x50000 in v1.9.0) *)
    stk rsegs mem lo (spZ regs) -> lo + NEXT_K <= spZ regs ->
    (symaddr ((Symbols.Plain.Sec.s_bss + Symbols.Plain.Sec.Size.s_bss + 0xfff) / 0x1000 * 0x1000)%Z) <= lo ->
    spZ regs <= 2 ^ 47 ->
    frm0 (@YK11.fp_csr fx) -> m_halted md = None -> m_vm_lazy md = [] -> fdchan (wz 2) ch_stderr md ->
    SRO rsegs (mkCfg (mkst regs (wz PCAP_SOURCE_NEXT) mem (seg_rom rsegs)) md) (psn_out h (swz =? 1) Fc cap p)
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

End K.
