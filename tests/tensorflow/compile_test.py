# Copyright 2019-2020 ETH Zurich and the DaCe authors. All rights reserved.
import pytest
import numpy as np


@pytest.mark.tensorflow
def test_compile():
    import tensorflow as tf
    from dace.frontend.tensorflow import TFSession

    print('DaCe Tensorflow frontend compile API test')

    A = np.random.rand(16, 16).astype(np.float32)
    B = np.random.rand(16, 16).astype(np.float32)

    A_tf = tf.placeholder(tf.float32, shape=[16, 16])
    B_tf = tf.placeholder(tf.float32, shape=[16, 16])

    with TFSession() as sess:
        # Simple matrix multiplication
        func = sess.compile(A_tf @ B_tf, False)
        func(feed_dict={A_tf: A, B_tf: B})
        C = func(feed_dict={A_tf: A, B_tf: B})

    diff = np.linalg.norm(C - (A @ B)) / (16 * 16)
    print("Difference:", diff)
    print("==== Program end ====")
    assert diff <= 1e-5


if __name__ == '__main__':
    try:
        import tensorflow
        test_compile()
    except ImportError:
        pass
